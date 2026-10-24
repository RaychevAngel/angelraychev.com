import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0724
import IrregularNine14P07C0725
import IrregularNine14P07C0726
import IrregularNine14P07C0727
import IrregularNine14P07C0728
import IrregularNine14P07C0729
import IrregularNine14P07C0730
import IrregularNine14P07C0731

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r44340 : Route 9 := (fun mask => (mask,id))

def c44340 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44340 : Upper (D 7) (R 7) [36,320,10] 13 := by
  apply FastRouting.sound _ _ [36,320,10] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44340 c44340
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43441
  · exact u43442
  · exact u43443
  · exact u43444
  · exact u43445
  · exact u43446
  · exact u43447
  · exact u43448
  · exact u43449
  · exact u43450
  · exact u43451
  · exact u43452
  · exact u43453
  · exact u43454
  · exact u43455

def r44341 : Route 9 := (fun mask => (mask,id))

def c44341 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44341 : Upper (D 7) (R 7) [36,320,24] 13 := by
  apply FastRouting.sound _ _ [36,320,24] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r44341 c44341
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43456
  · exact u43457
  · exact u43458
  · exact u43459
  · exact u43460
  · exact u43461
  · exact u43462
  · exact u43463
  · exact u43464
  · exact u43465

def b44342 : PairBound 9 := { available := 219, camps := [{ cop := 5, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 322 37 219 219 251 219 219 475), lower := (rows 37 322 37 8 16 32 64 128 256), losses := [] }

theorem u44342 : Upper (D 7) (R 7) [36,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44343 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 322 38 219 219 251 219 219 475), lower := (rows 37 322 38 8 16 32 64 128 256), losses := [] }

theorem u44343 : Upper (D 7) (R 7) [36,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44344 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 322 44 219 211 243 211 211 467), lower := (rows 37 322 44 8 16 32 64 128 256), losses := [] }

theorem u44344 : Upper (D 7) (R 7) [36,320,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44345 : Route 9 := (fun mask => (mask,id))

def c44345 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u44345 : Upper (D 7) (R 7) [36,320,65] 13 := by
  apply FastRouting.sound _ _ [36,320,65] 13 (by decide) (choices 2) [3,17,18,33,34,48,129,130,144,160] r44345 c44345
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43466
  · exact u43467
  · exact u43468
  · exact u43469
  · exact u43470
  · exact u43471
  · exact u43472
  · exact u43473
  · exact u43474
  · exact u43475

def b44346 : PairBound 9 := { available := 187, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 37 322 70 187 187 187 251 187 443), lower := (rows 37 322 70 8 16 32 64 128 256), losses := [] }

theorem u44346 : Upper (D 7) (R 7) [36,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44347 : Route 9 := (fun mask => (mask,id))

def c44347 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u44347 : Upper (D 7) (R 7) [36,320,72] 13 := by
  apply FastRouting.sound _ _ [36,320,72] 13 (by decide) (choices 2) [3,17,18,33,34,48,129,130,144,160] r44347 c44347
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43476
  · exact u43477
  · exact u43478
  · exact u43479
  · exact u43480
  · exact u43481
  · exact u43482
  · exact u43483
  · exact u43484
  · exact u43485

def b44348 : PairBound 9 := { available := 155, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 322 100 155 155 187 219 155 411), lower := (rows 37 322 100 8 16 32 64 128 256), losses := [] }

theorem u44348 : Upper (D 7) (R 7) [36,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44348 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44349 : Route 9 := (fun mask => (mask,id))

def c44349 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44349 : Upper (D 7) (R 7) [36,320,129] 13 := by
  apply FastRouting.sound _ _ [36,320,129] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44349 c44349
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43486
  · exact u43487
  · exact u43488
  · exact u43489
  · exact u43490
  · exact u43491
  · exact u43492
  · exact u43493
  · exact u43494
  · exact u43495
  · exact u43496
  · exact u43497
  · exact u43498
  · exact u43499
  · exact u43500

def r44350 : Route 9 := (fun mask => (mask,id))

def c44350 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44350 : Upper (D 7) (R 7) [36,320,130] 13 := by
  apply FastRouting.sound _ _ [36,320,130] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44350 c44350
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43501
  · exact u43502
  · exact u43503
  · exact u43504
  · exact u43505
  · exact u43506
  · exact u43507
  · exact u43508
  · exact u43509
  · exact u43510
  · exact u43511
  · exact u43512
  · exact u43513
  · exact u43514
  · exact u43515

def r44351 : Route 9 := (fun mask => (mask,id))

def c44351 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44351 : Upper (D 7) (R 7) [36,320,136] 13 := by
  apply FastRouting.sound _ _ [36,320,136] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r44351 c44351
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43516
  · exact u43517
  · exact u43518
  · exact u43519
  · exact u43520
  · exact u43521
  · exact u43522
  · exact u43523
  · exact u43524
  · exact u43525
  · exact u43526
  · exact u43527
  · exact u43528
  · exact u43529
  · exact u43530

def b44352 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 474, targets := 32 },{ cop := 2, region := 1, targets := 2 }], pairs := [(0,1),(1,5),(3,5),(4,5)], upper := (rows 37 322 164 219 219 251 219 219 475), lower := (rows 37 322 164 8 16 32 64 128 256), losses := [] }

theorem u44352 : Upper (D 7) (R 7) [36,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44353 : Route 9 := (fun mask => (mask,id))

def c44353 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u44353 : Upper (D 7) (R 7) [36,320,192] 13 := by
  apply FastRouting.sound _ _ [36,320,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,129,130,144,160] r44353 c44353
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43531
  · exact u43532
  · exact u43533
  · exact u43534
  · exact u43535
  · exact u43536
  · exact u43537
  · exact u43538
  · exact u43539
  · exact u43540

theorem m44354_6 : Upper (D 7) (R 7) [96,160,3,6] 13 :=
  permutation_upper _ _ _ [96,160,3,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43542

theorem m44354_18 : Upper (D 7) (R 7) [96,160,3,18] 13 :=
  permutation_upper _ _ _ [96,160,3,17] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43543

theorem m44354_129 : Upper (D 7) (R 7) [96,160,3,129] 13 :=
  permutation_upper _ _ _ [96,160,3,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43546

theorem m44354_130 : Upper (D 7) (R 7) [96,160,3,130] 13 :=
  permutation_upper _ _ _ [96,160,3,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43545

theorem m44354_132 : Upper (D 7) (R 7) [96,160,3,132] 13 :=
  permutation_upper _ _ _ [96,160,3,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43547

theorem m44354_144 : Upper (D 7) (R 7) [96,160,3,144] 13 :=
  permutation_upper _ _ _ [96,160,3,80] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43548

theorem m44354_258 : Upper (D 7) (R 7) [96,160,3,258] 13 :=
  permutation_upper _ _ _ [96,160,3,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43550

theorem m44354_384 : Upper (D 7) (R 7) [96,160,3,384] 13 :=
  permutation_upper _ _ _ [96,160,3,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43553

def r44354 : Route 9 := (fun mask => (mask,id))

def c44354 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44354 : Upper (D 7) (R 7) [96,160,3] 13 := by
  apply FastRouting.sound _ _ [96,160,3] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192,257,258,260,272,320,384] r44354 c44354
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43541
  · exact u43542
  · exact m44354_6
  · exact u43543
  · exact m44354_18
  · exact u43544
  · exact u43545
  · exact u43546
  · exact u43547
  · exact u43548
  · exact m44354_129
  · exact m44354_130
  · exact m44354_132
  · exact m44354_144
  · exact u43549
  · exact u43550
  · exact m44354_258
  · exact u43551
  · exact u43552
  · exact u43553
  · exact m44354_384

theorem m44355_3 : Upper (D 7) (R 7) [96,160,9,3] 13 :=
  permutation_upper _ _ _ [96,160,3,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43542

def r44355 : Route 9 := (fun mask => (mask,id))

def c44355 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44355 : Upper (D 7) (R 7) [96,160,9] 13 := by
  apply FastRouting.sound _ _ [96,160,9] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192,257,258,260,272,320,384] r44355 c44355
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44355_3
  · exact u43554
  · exact u43555
  · exact u43556
  · exact u43557
  · exact u43558
  · exact u43559
  · exact u43560
  · exact u43561
  · exact u43562
  · exact u43563
  · exact u43564
  · exact u43565
  · exact u43566
  · exact u43567
  · exact u43568
  · exact u43569
  · exact u43570
  · exact u43571
  · exact u43572
  · exact u43573

theorem m44356_3 : Upper (D 7) (R 7) [96,160,24,3] 13 :=
  permutation_upper _ _ _ [96,160,3,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43544

theorem m44356_5 : Upper (D 7) (R 7) [96,160,24,5] 13 :=
  permutation_upper _ _ _ [96,160,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43558

theorem m44356_6 : Upper (D 7) (R 7) [96,160,24,6] 13 :=
  permutation_upper _ _ _ [96,160,9,20] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43558

theorem m44356_129 : Upper (D 7) (R 7) [96,160,24,129] 13 :=
  permutation_upper _ _ _ [96,160,24,66] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43585

theorem m44356_130 : Upper (D 7) (R 7) [96,160,24,130] 13 :=
  permutation_upper _ _ _ [96,160,24,65] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43584

theorem m44356_132 : Upper (D 7) (R 7) [96,160,24,132] 13 :=
  permutation_upper _ _ _ [96,160,24,68] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43586

theorem m44356_258 : Upper (D 7) (R 7) [96,160,24,258] 13 :=
  permutation_upper _ _ _ [96,160,24,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43588

theorem m44356_384 : Upper (D 7) (R 7) [96,160,24,384] 13 :=
  permutation_upper _ _ _ [96,160,24,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43590

def r44356 : Route 9 := (fun mask => (mask,id))

def c44356 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 18 => 4 | 34 => 5 | 20 => 4 | 36 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u44356 : Upper (D 7) (R 7) [96,160,24] 13 := by
  apply FastRouting.sound _ _ [96,160,24] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,257,258,260,320,384] r44356 c44356
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44356_3
  · exact m44356_5
  · exact m44356_6
  · exact u43584
  · exact u43585
  · exact u43586
  · exact m44356_129
  · exact m44356_130
  · exact m44356_132
  · exact u43587
  · exact u43588
  · exact m44356_258
  · exact u43589
  · exact u43590
  · exact m44356_384

def b44357 : PairBound 9 := { available := 415, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 162 69 415 415 447 479 415 415), lower := (rows 97 162 69 8 16 32 64 128 256), losses := [] }

theorem u44357 : Upper (D 7) (R 7) [96,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m44358_3 : Upper (D 7) (R 7) [96,160,66,3] 13 :=
  permutation_upper _ _ _ [96,160,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43546

theorem m44358_5 : Upper (D 7) (R 7) [96,160,66,5] 13 :=
  permutation_upper _ _ _ [96,160,9,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43560

theorem m44358_6 : Upper (D 7) (R 7) [96,160,66,6] 13 :=
  permutation_upper _ _ _ [96,160,9,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43563

theorem m44358_17 : Upper (D 7) (R 7) [96,160,66,17] 13 :=
  permutation_upper _ _ _ [96,160,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43574

theorem m44358_18 : Upper (D 7) (R 7) [96,160,66,18] 13 :=
  permutation_upper _ _ _ [96,160,17,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43576

theorem m44358_20 : Upper (D 7) (R 7) [96,160,66,20] 13 :=
  permutation_upper _ _ _ [96,160,24,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43585

theorem m44358_130 : Upper (D 7) (R 7) [96,160,66,130] 13 :=
  permutation_upper _ _ _ [96,160,65,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43591

def r44358 : Route 9 := (fun mask => (mask,id))

def c44358 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u44358 : Upper (D 7) (R 7) [96,160,66] 13 := by
  apply FastRouting.sound _ _ [96,160,66] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,257,258,260,272,384] r44358 c44358
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44358_3
  · exact m44358_5
  · exact m44358_6
  · exact m44358_17
  · exact m44358_18
  · exact m44358_20
  · exact u43597
  · exact m44358_130
  · exact u43598
  · exact u43599
  · exact u43600
  · exact u43601
  · exact u43602
  · exact u43603
  · exact u43604

theorem m44359_3 : Upper (D 7) (R 7) [96,160,72,3] 13 :=
  permutation_upper _ _ _ [96,160,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43547

theorem m44359_5 : Upper (D 7) (R 7) [96,160,72,5] 13 :=
  permutation_upper _ _ _ [96,160,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43561

theorem m44359_6 : Upper (D 7) (R 7) [96,160,72,6] 13 :=
  permutation_upper _ _ _ [96,160,9,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43565

theorem m44359_17 : Upper (D 7) (R 7) [96,160,72,17] 13 :=
  permutation_upper _ _ _ [96,160,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43575

theorem m44359_18 : Upper (D 7) (R 7) [96,160,72,18] 13 :=
  permutation_upper _ _ _ [96,160,17,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43577

theorem m44359_20 : Upper (D 7) (R 7) [96,160,72,20] 13 :=
  permutation_upper _ _ _ [96,160,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43586

theorem m44359_129 : Upper (D 7) (R 7) [96,160,72,129] 13 :=
  permutation_upper _ _ _ [96,160,66,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43598

theorem m44359_130 : Upper (D 7) (R 7) [96,160,72,130] 13 :=
  permutation_upper _ _ _ [96,160,65,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43592

def r44359 : Route 9 := (fun mask => (mask,id))

def c44359 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u44359 : Upper (D 7) (R 7) [96,160,72] 13 := by
  apply FastRouting.sound _ _ [96,160,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,257,258,260,272,384] r44359 c44359
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44359_3
  · exact m44359_5
  · exact m44359_6
  · exact m44359_17
  · exact m44359_18
  · exact m44359_20
  · exact m44359_129
  · exact m44359_130
  · exact u43605
  · exact u43606
  · exact u43607
  · exact u43608
  · exact u43609
  · exact u43610
  · exact u43611

theorem m44360_3 : Upper (D 7) (R 7) [96,160,192,3] 13 :=
  permutation_upper _ _ _ [96,160,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43549

theorem m44360_5 : Upper (D 7) (R 7) [96,160,192,5] 13 :=
  permutation_upper _ _ _ [96,160,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43567

theorem m44360_6 : Upper (D 7) (R 7) [96,160,192,6] 13 :=
  permutation_upper _ _ _ [96,160,9,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43567

theorem m44360_17 : Upper (D 7) (R 7) [96,160,192,17] 13 :=
  permutation_upper _ _ _ [96,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43578

theorem m44360_18 : Upper (D 7) (R 7) [96,160,192,18] 13 :=
  permutation_upper _ _ _ [96,160,17,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43578

theorem m44360_20 : Upper (D 7) (R 7) [96,160,192,20] 13 :=
  permutation_upper _ _ _ [96,160,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43587

theorem m44360_258 : Upper (D 7) (R 7) [96,160,192,258] 13 :=
  permutation_upper _ _ _ [96,160,192,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43616

def r44360 : Route 9 := (fun mask => (mask,id))

def c44360 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u44360 : Upper (D 7) (R 7) [96,160,192] 13 := by
  apply FastRouting.sound _ _ [96,160,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r44360 c44360
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44360_3
  · exact m44360_5
  · exact m44360_6
  · exact m44360_17
  · exact m44360_18
  · exact m44360_20
  · exact u43616
  · exact m44360_258
  · exact u43617
  · exact u43618

theorem m44361_3 : Upper (D 7) (R 7) [96,160,257,3] 13 :=
  permutation_upper _ _ _ [96,160,3,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43550

theorem m44361_5 : Upper (D 7) (R 7) [96,160,257,5] 13 :=
  permutation_upper _ _ _ [96,160,9,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43568

theorem m44361_6 : Upper (D 7) (R 7) [96,160,257,6] 13 :=
  permutation_upper _ _ _ [96,160,9,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43569

theorem m44361_17 : Upper (D 7) (R 7) [96,160,257,17] 13 :=
  permutation_upper _ _ _ [96,160,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43579

theorem m44361_18 : Upper (D 7) (R 7) [96,160,257,18] 13 :=
  permutation_upper _ _ _ [96,160,17,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43580

theorem m44361_20 : Upper (D 7) (R 7) [96,160,257,20] 13 :=
  permutation_upper _ _ _ [96,160,24,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43588

theorem m44361_65 : Upper (D 7) (R 7) [96,160,257,65] 13 :=
  permutation_upper _ _ _ [96,160,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43593

theorem m44361_66 : Upper (D 7) (R 7) [96,160,257,66] 13 :=
  permutation_upper _ _ _ [96,160,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43600

theorem m44361_68 : Upper (D 7) (R 7) [96,160,257,68] 13 :=
  permutation_upper _ _ _ [96,160,72,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43607

theorem m44361_80 : Upper (D 7) (R 7) [96,160,257,80] 13 :=
  permutation_upper _ _ _ [96,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43612

theorem m44361_129 : Upper (D 7) (R 7) [96,160,257,129] 13 :=
  permutation_upper _ _ _ [96,160,66,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43601

theorem m44361_130 : Upper (D 7) (R 7) [96,160,257,130] 13 :=
  permutation_upper _ _ _ [96,160,65,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43594

theorem m44361_132 : Upper (D 7) (R 7) [96,160,257,132] 13 :=
  permutation_upper _ _ _ [96,160,72,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43608

theorem m44361_144 : Upper (D 7) (R 7) [96,160,257,144] 13 :=
  permutation_upper _ _ _ [96,160,80,258] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43613

theorem m44361_192 : Upper (D 7) (R 7) [96,160,257,192] 13 :=
  permutation_upper _ _ _ [96,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43616

def r44361 : Route 9 := (fun mask => (mask,id))

def c44361 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44361 : Upper (D 7) (R 7) [96,160,257] 13 := by
  apply FastRouting.sound _ _ [96,160,257] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44361 c44361
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44361_3
  · exact m44361_5
  · exact m44361_6
  · exact m44361_17
  · exact m44361_18
  · exact m44361_20
  · exact m44361_65
  · exact m44361_66
  · exact m44361_68
  · exact m44361_80
  · exact m44361_129
  · exact m44361_130
  · exact m44361_132
  · exact m44361_144
  · exact m44361_192

theorem m44362_3 : Upper (D 7) (R 7) [96,160,264,3] 13 :=
  permutation_upper _ _ _ [96,160,3,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43551

theorem m44362_5 : Upper (D 7) (R 7) [96,160,264,5] 13 :=
  permutation_upper _ _ _ [96,160,9,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43570

theorem m44362_6 : Upper (D 7) (R 7) [96,160,264,6] 13 :=
  permutation_upper _ _ _ [96,160,9,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43570

theorem m44362_17 : Upper (D 7) (R 7) [96,160,264,17] 13 :=
  permutation_upper _ _ _ [96,160,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43581

theorem m44362_18 : Upper (D 7) (R 7) [96,160,264,18] 13 :=
  permutation_upper _ _ _ [96,160,17,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43581

theorem m44362_20 : Upper (D 7) (R 7) [96,160,264,20] 13 :=
  permutation_upper _ _ _ [96,160,24,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43589

theorem m44362_65 : Upper (D 7) (R 7) [96,160,264,65] 13 :=
  permutation_upper _ _ _ [96,160,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43595

theorem m44362_66 : Upper (D 7) (R 7) [96,160,264,66] 13 :=
  permutation_upper _ _ _ [96,160,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43602

theorem m44362_68 : Upper (D 7) (R 7) [96,160,264,68] 13 :=
  permutation_upper _ _ _ [96,160,72,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43609

theorem m44362_80 : Upper (D 7) (R 7) [96,160,264,80] 13 :=
  permutation_upper _ _ _ [96,160,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43614

theorem m44362_129 : Upper (D 7) (R 7) [96,160,264,129] 13 :=
  permutation_upper _ _ _ [96,160,66,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43602

theorem m44362_130 : Upper (D 7) (R 7) [96,160,264,130] 13 :=
  permutation_upper _ _ _ [96,160,65,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43595

theorem m44362_132 : Upper (D 7) (R 7) [96,160,264,132] 13 :=
  permutation_upper _ _ _ [96,160,72,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43609

theorem m44362_144 : Upper (D 7) (R 7) [96,160,264,144] 13 :=
  permutation_upper _ _ _ [96,160,80,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43614

theorem m44362_192 : Upper (D 7) (R 7) [96,160,264,192] 13 :=
  permutation_upper _ _ _ [96,160,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43617

def r44362 : Route 9 := (fun mask => (mask,id))

def c44362 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44362 : Upper (D 7) (R 7) [96,160,264] 13 := by
  apply FastRouting.sound _ _ [96,160,264] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44362 c44362
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44362_3
  · exact m44362_5
  · exact m44362_6
  · exact m44362_17
  · exact m44362_18
  · exact m44362_20
  · exact m44362_65
  · exact m44362_66
  · exact m44362_68
  · exact m44362_80
  · exact m44362_129
  · exact m44362_130
  · exact m44362_132
  · exact m44362_144
  · exact m44362_192

theorem m44363_3 : Upper (D 7) (R 7) [96,160,320,3] 13 :=
  permutation_upper _ _ _ [96,160,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43553

theorem m44363_5 : Upper (D 7) (R 7) [96,160,320,5] 13 :=
  permutation_upper _ _ _ [96,160,9,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43572

theorem m44363_6 : Upper (D 7) (R 7) [96,160,320,6] 13 :=
  permutation_upper _ _ _ [96,160,9,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43573

theorem m44363_17 : Upper (D 7) (R 7) [96,160,320,17] 13 :=
  permutation_upper _ _ _ [96,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43582

theorem m44363_18 : Upper (D 7) (R 7) [96,160,320,18] 13 :=
  permutation_upper _ _ _ [96,160,17,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43583

theorem m44363_20 : Upper (D 7) (R 7) [96,160,320,20] 13 :=
  permutation_upper _ _ _ [96,160,24,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43590

theorem m44363_129 : Upper (D 7) (R 7) [96,160,320,129] 13 :=
  permutation_upper _ _ _ [96,160,66,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43604

theorem m44363_130 : Upper (D 7) (R 7) [96,160,320,130] 13 :=
  permutation_upper _ _ _ [96,160,65,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43596

theorem m44363_132 : Upper (D 7) (R 7) [96,160,320,132] 13 :=
  permutation_upper _ _ _ [96,160,72,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43611

theorem m44363_144 : Upper (D 7) (R 7) [96,160,320,144] 13 :=
  permutation_upper _ _ _ [96,160,80,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43615

def r44363 : Route 9 := (fun mask => (mask,id))

def c44363 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 48 => 5 | 80 => 6 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u44363 : Upper (D 7) (R 7) [96,160,320] 13 := by
  apply FastRouting.sound _ _ [96,160,320] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144] r44363 c44363
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44363_3
  · exact m44363_5
  · exact m44363_6
  · exact m44363_17
  · exact m44363_18
  · exact m44363_20
  · exact m44363_129
  · exact m44363_130
  · exact m44363_132
  · exact m44363_144

def b44364 : PairBound 9 := { available := 254, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 97 259 7 254 254 254 254 254 510), lower := (rows 97 259 7 8 16 32 64 128 256), losses := [] }

theorem u44364 : Upper (D 7) (R 7) [96,257,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44365 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44365 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44365 : Upper (D 7) (R 7) [96,257,9] 13 := by
  apply FastRouting.sound _ _ [96,257,9] 13 (by decide) (choices 2) [6,18,20,34,36,48,96,130,132,144,160] r44365 c44365
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43626
  · exact u43627
  · exact u43628
  · exact u43629
  · exact u43630
  · exact u43631
  · exact u43632
  · exact u43633
  · exact u43634
  · exact u43635
  · exact u43636

theorem m44366_3 : Upper (D 7) (R 7) [96,257,10,3] 13 :=
  permutation_upper _ _ _ [96,257,3,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43619

theorem m44366_5 : Upper (D 7) (R 7) [96,257,10,5] 13 :=
  permutation_upper _ _ _ [96,257,9,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43626

def r44366 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44366 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44366 : Upper (D 7) (R 7) [96,257,10] 13 := by
  apply FastRouting.sound _ _ [96,257,10] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,129,130,132,144,160] r44366 c44366
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44366_3
  · exact m44366_5
  · exact u43637
  · exact u43638
  · exact u43639
  · exact u43640
  · exact u43641
  · exact u43642
  · exact u43643
  · exact u43644
  · exact u43645
  · exact u43646
  · exact u43647
  · exact u43648
  · exact u43649
  · exact u43650

theorem m44367_3 : Upper (D 7) (R 7) [96,257,24,3] 13 :=
  permutation_upper _ _ _ [96,257,3,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43620

theorem m44367_5 : Upper (D 7) (R 7) [96,257,24,5] 13 :=
  permutation_upper _ _ _ [96,257,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43628

theorem m44367_6 : Upper (D 7) (R 7) [96,257,24,6] 13 :=
  permutation_upper _ _ _ [96,257,10,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43640

def r44367 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44367 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44367 : Upper (D 7) (R 7) [96,257,24] 13 := by
  apply FastRouting.sound _ _ [96,257,24] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160] r44367 c44367
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44367_3
  · exact m44367_5
  · exact m44367_6
  · exact u43662
  · exact u43663
  · exact u43664
  · exact u43665
  · exact u43666
  · exact u43667
  · exact u43668
  · exact u43669

def b44368 : PairBound 9 := { available := 222, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 259 37 222 222 254 222 222 478), lower := (rows 97 259 37 8 16 32 64 128 256), losses := [] }

theorem u44368 : Upper (D 7) (R 7) [96,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m44369_3 : Upper (D 7) (R 7) [96,257,34,3] 13 :=
  permutation_upper _ _ _ [96,257,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43621

theorem m44369_5 : Upper (D 7) (R 7) [96,257,34,5] 13 :=
  permutation_upper _ _ _ [96,257,9,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43629

theorem m44369_6 : Upper (D 7) (R 7) [96,257,34,6] 13 :=
  permutation_upper _ _ _ [96,257,10,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43642

theorem m44369_17 : Upper (D 7) (R 7) [96,257,34,17] 13 :=
  permutation_upper _ _ _ [96,257,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43651

theorem m44369_18 : Upper (D 7) (R 7) [96,257,34,18] 13 :=
  permutation_upper _ _ _ [96,257,18,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43656

theorem m44369_20 : Upper (D 7) (R 7) [96,257,34,20] 13 :=
  permutation_upper _ _ _ [96,257,24,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43663

theorem m44369_65 : Upper (D 7) (R 7) [96,257,34,65] 13 :=
  permutation_upper _ _ _ [96,257,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43670

def r44369 : Route 9 := (fun mask => (mask,id))

def c44369 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44369 : Upper (D 7) (R 7) [96,257,34] 13 := by
  apply FastRouting.sound _ _ [96,257,34] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44369 c44369
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44369_3
  · exact m44369_5
  · exact m44369_6
  · exact m44369_17
  · exact m44369_18
  · exact m44369_20
  · exact m44369_65
  · exact u43675
  · exact u43676
  · exact u43677
  · exact u43678
  · exact u43679
  · exact u43680
  · exact u43681
  · exact u43682

theorem m44370_3 : Upper (D 7) (R 7) [96,257,40,3] 13 :=
  permutation_upper _ _ _ [96,257,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43622

theorem m44370_5 : Upper (D 7) (R 7) [96,257,40,5] 13 :=
  permutation_upper _ _ _ [96,257,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43630

theorem m44370_6 : Upper (D 7) (R 7) [96,257,40,6] 13 :=
  permutation_upper _ _ _ [96,257,10,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43643

theorem m44370_17 : Upper (D 7) (R 7) [96,257,40,17] 13 :=
  permutation_upper _ _ _ [96,257,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43652

theorem m44370_18 : Upper (D 7) (R 7) [96,257,40,18] 13 :=
  permutation_upper _ _ _ [96,257,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43657

theorem m44370_20 : Upper (D 7) (R 7) [96,257,40,20] 13 :=
  permutation_upper _ _ _ [96,257,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43664

theorem m44370_65 : Upper (D 7) (R 7) [96,257,40,65] 13 :=
  permutation_upper _ _ _ [96,257,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43671

theorem m44370_66 : Upper (D 7) (R 7) [96,257,40,66] 13 :=
  permutation_upper _ _ _ [96,257,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43676

def r44370 : Route 9 := (fun mask => (mask,id))

def c44370 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44370 : Upper (D 7) (R 7) [96,257,40] 13 := by
  apply FastRouting.sound _ _ [96,257,40] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44370 c44370
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44370_3
  · exact m44370_5
  · exact m44370_6
  · exact m44370_17
  · exact m44370_18
  · exact m44370_20
  · exact m44370_65
  · exact m44370_66
  · exact u43683
  · exact u43684
  · exact u43685
  · exact u43686
  · exact u43687
  · exact u43688
  · exact u43689

def b44371 : PairBound 9 := { available := 159, camps := [{ cop := 0, region := 4, targets := 130 },{ cop := 2, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 259 100 159 159 191 223 159 415), lower := (rows 97 259 100 8 16 32 64 128 256), losses := [] }

theorem u44371 : Upper (D 7) (R 7) [96,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m44372_6 : Upper (D 7) (R 7) [96,257,129,6] 13 :=
  permutation_upper _ _ _ [96,257,10,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43646

theorem m44372_18 : Upper (D 7) (R 7) [96,257,129,18] 13 :=
  permutation_upper _ _ _ [96,257,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43658

theorem m44372_20 : Upper (D 7) (R 7) [96,257,129,20] 13 :=
  permutation_upper _ _ _ [96,257,24,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43666

theorem m44372_34 : Upper (D 7) (R 7) [96,257,129,34] 13 :=
  permutation_upper _ _ _ [96,257,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43678

theorem m44372_36 : Upper (D 7) (R 7) [96,257,129,36] 13 :=
  permutation_upper _ _ _ [96,257,40,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43685

theorem m44372_48 : Upper (D 7) (R 7) [96,257,129,48] 13 :=
  permutation_upper _ _ _ [96,257,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43690

theorem m44372_96 : Upper (D 7) (R 7) [96,257,129,96] 13 :=
  permutation_upper _ _ _ [96,257,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43694

def r44372 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44372 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44372 : Upper (D 7) (R 7) [96,257,129] 13 := by
  apply FastRouting.sound _ _ [96,257,129] 13 (by decide) (choices 2) [6,18,20,34,36,48,96,130,132,144,160] r44372 c44372
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44372_6
  · exact m44372_18
  · exact m44372_20
  · exact m44372_34
  · exact m44372_36
  · exact m44372_48
  · exact m44372_96
  · exact u43697
  · exact u43698
  · exact u43699
  · exact u43700

theorem m44373_3 : Upper (D 7) (R 7) [96,257,130,3] 13 :=
  permutation_upper _ _ _ [96,257,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43623

theorem m44373_5 : Upper (D 7) (R 7) [96,257,130,5] 13 :=
  permutation_upper _ _ _ [96,257,9,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43633

theorem m44373_6 : Upper (D 7) (R 7) [96,257,130,6] 13 :=
  permutation_upper _ _ _ [96,257,10,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43647

theorem m44373_17 : Upper (D 7) (R 7) [96,257,130,17] 13 :=
  permutation_upper _ _ _ [96,257,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43653

theorem m44373_18 : Upper (D 7) (R 7) [96,257,130,18] 13 :=
  permutation_upper _ _ _ [96,257,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43659

theorem m44373_20 : Upper (D 7) (R 7) [96,257,130,20] 13 :=
  permutation_upper _ _ _ [96,257,24,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43667

theorem m44373_33 : Upper (D 7) (R 7) [96,257,130,33] 13 :=
  permutation_upper _ _ _ [96,257,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43672

theorem m44373_34 : Upper (D 7) (R 7) [96,257,130,34] 13 :=
  permutation_upper _ _ _ [96,257,34,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43679

theorem m44373_36 : Upper (D 7) (R 7) [96,257,130,36] 13 :=
  permutation_upper _ _ _ [96,257,40,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43686

theorem m44373_48 : Upper (D 7) (R 7) [96,257,130,48] 13 :=
  permutation_upper _ _ _ [96,257,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43691

theorem m44373_96 : Upper (D 7) (R 7) [96,257,130,96] 13 :=
  permutation_upper _ _ _ [96,257,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43695

theorem m44373_129 : Upper (D 7) (R 7) [96,257,130,129] 13 :=
  permutation_upper _ _ _ [96,257,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43697

def r44373 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44373 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44373 : Upper (D 7) (R 7) [96,257,130] 13 := by
  apply FastRouting.sound _ _ [96,257,130] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,129,130,132,144,160] r44373 c44373
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44373_3
  · exact m44373_5
  · exact m44373_6
  · exact m44373_17
  · exact m44373_18
  · exact m44373_20
  · exact m44373_33
  · exact m44373_34
  · exact m44373_36
  · exact m44373_48
  · exact m44373_96
  · exact m44373_129
  · exact u43701
  · exact u43702
  · exact u43703
  · exact u43704

theorem m44374_3 : Upper (D 7) (R 7) [96,257,136,3] 13 :=
  permutation_upper _ _ _ [96,257,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43624

theorem m44374_5 : Upper (D 7) (R 7) [96,257,136,5] 13 :=
  permutation_upper _ _ _ [96,257,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43634

theorem m44374_6 : Upper (D 7) (R 7) [96,257,136,6] 13 :=
  permutation_upper _ _ _ [96,257,10,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43648

theorem m44374_17 : Upper (D 7) (R 7) [96,257,136,17] 13 :=
  permutation_upper _ _ _ [96,257,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43654

theorem m44374_18 : Upper (D 7) (R 7) [96,257,136,18] 13 :=
  permutation_upper _ _ _ [96,257,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43660

theorem m44374_20 : Upper (D 7) (R 7) [96,257,136,20] 13 :=
  permutation_upper _ _ _ [96,257,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43668

theorem m44374_33 : Upper (D 7) (R 7) [96,257,136,33] 13 :=
  permutation_upper _ _ _ [96,257,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43673

theorem m44374_34 : Upper (D 7) (R 7) [96,257,136,34] 13 :=
  permutation_upper _ _ _ [96,257,34,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43680

theorem m44374_36 : Upper (D 7) (R 7) [96,257,136,36] 13 :=
  permutation_upper _ _ _ [96,257,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43687

theorem m44374_48 : Upper (D 7) (R 7) [96,257,136,48] 13 :=
  permutation_upper _ _ _ [96,257,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43692

theorem m44374_96 : Upper (D 7) (R 7) [96,257,136,96] 13 :=
  permutation_upper _ _ _ [96,257,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43696

theorem m44374_129 : Upper (D 7) (R 7) [96,257,136,129] 13 :=
  permutation_upper _ _ _ [96,257,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43698

theorem m44374_130 : Upper (D 7) (R 7) [96,257,136,130] 13 :=
  permutation_upper _ _ _ [96,257,130,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43702

def r44374 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44374 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44374 : Upper (D 7) (R 7) [96,257,136] 13 := by
  apply FastRouting.sound _ _ [96,257,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,129,130,132,144,160] r44374 c44374
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44374_3
  · exact m44374_5
  · exact m44374_6
  · exact m44374_17
  · exact m44374_18
  · exact m44374_20
  · exact m44374_33
  · exact m44374_34
  · exact m44374_36
  · exact m44374_48
  · exact m44374_96
  · exact m44374_129
  · exact m44374_130
  · exact u43705
  · exact u43706
  · exact u43707

theorem m44375_3 : Upper (D 7) (R 7) [96,257,160,3] 13 :=
  permutation_upper _ _ _ [96,257,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43625

theorem m44375_5 : Upper (D 7) (R 7) [96,257,160,5] 13 :=
  permutation_upper _ _ _ [96,257,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43636

theorem m44375_6 : Upper (D 7) (R 7) [96,257,160,6] 13 :=
  permutation_upper _ _ _ [96,257,10,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43650

theorem m44375_17 : Upper (D 7) (R 7) [96,257,160,17] 13 :=
  permutation_upper _ _ _ [96,257,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43655

theorem m44375_18 : Upper (D 7) (R 7) [96,257,160,18] 13 :=
  permutation_upper _ _ _ [96,257,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43661

theorem m44375_20 : Upper (D 7) (R 7) [96,257,160,20] 13 :=
  permutation_upper _ _ _ [96,257,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43669

theorem m44375_65 : Upper (D 7) (R 7) [96,257,160,65] 13 :=
  permutation_upper _ _ _ [96,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43674

theorem m44375_66 : Upper (D 7) (R 7) [96,257,160,66] 13 :=
  permutation_upper _ _ _ [96,257,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43682

theorem m44375_68 : Upper (D 7) (R 7) [96,257,160,68] 13 :=
  permutation_upper _ _ _ [96,257,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43689

theorem m44375_80 : Upper (D 7) (R 7) [96,257,160,80] 13 :=
  permutation_upper _ _ _ [96,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43693

theorem m44375_129 : Upper (D 7) (R 7) [96,257,160,129] 13 :=
  permutation_upper _ _ _ [96,257,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43700

theorem m44375_130 : Upper (D 7) (R 7) [96,257,160,130] 13 :=
  permutation_upper _ _ _ [96,257,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43704

theorem m44375_132 : Upper (D 7) (R 7) [96,257,160,132] 13 :=
  permutation_upper _ _ _ [96,257,136,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43707

theorem m44375_144 : Upper (D 7) (R 7) [96,257,160,144] 13 :=
  permutation_upper _ _ _ [96,257,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43708

def r44375 : Route 9 := (fun mask => (mask,id))

def c44375 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44375 : Upper (D 7) (R 7) [96,257,160] 13 := by
  apply FastRouting.sound _ _ [96,257,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44375 c44375
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44375_3
  · exact m44375_5
  · exact m44375_6
  · exact m44375_17
  · exact m44375_18
  · exact m44375_20
  · exact m44375_65
  · exact m44375_66
  · exact m44375_68
  · exact m44375_80
  · exact m44375_129
  · exact m44375_130
  · exact m44375_132
  · exact m44375_144
  · exact u43709

def r44376 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44376 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44376 : Upper (D 7) (R 7) [96,260,3] 13 := by
  apply FastRouting.sound _ _ [96,260,3] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r44376 c44376
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43710
  · exact u43711
  · exact u43712
  · exact u43713
  · exact u43714
  · exact u43715
  · exact u43716
  · exact u43717
  · exact u43718
  · exact u43719
  · exact u43720

def r44377 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44377 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44377 : Upper (D 7) (R 7) [96,260,9] 13 := by
  apply FastRouting.sound _ _ [96,260,9] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r44377 c44377
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43721
  · exact u43722
  · exact u43723
  · exact u43724
  · exact u43725
  · exact u43726
  · exact u43727
  · exact u43728
  · exact u43729
  · exact u43730
  · exact u43731

def r44378 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44378 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44378 : Upper (D 7) (R 7) [96,260,10] 13 := by
  apply FastRouting.sound _ _ [96,260,10] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r44378 c44378
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43732
  · exact u43733
  · exact u43734
  · exact u43735
  · exact u43736
  · exact u43737
  · exact u43738
  · exact u43739
  · exact u43740
  · exact u43741
  · exact u43742

def r44379 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44379 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44379 : Upper (D 7) (R 7) [96,260,24] 13 := by
  apply FastRouting.sound _ _ [96,260,24] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r44379 c44379
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43743
  · exact u43744
  · exact u43745
  · exact u43746
  · exact u43747
  · exact u43748
  · exact u43749

def b44380 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 4, targets := 194 },{ cop := 2, region := 474, targets := 32 }], pairs := [(1,5),(2,1),(2,6),(2,7)], upper := (rows 97 262 37 219 219 251 219 219 475), lower := (rows 97 262 37 8 16 32 64 128 256), losses := [] }

theorem u44380 : Upper (D 7) (R 7) [96,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44381 : Route 9 := (fun mask => (mask,id))

def c44381 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44381 : Upper (D 7) (R 7) [96,260,34] 13 := by
  apply FastRouting.sound _ _ [96,260,34] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r44381 c44381
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43750
  · exact u43751
  · exact u43752
  · exact u43753
  · exact u43754
  · exact u43755
  · exact u43756
  · exact u43757
  · exact u43758
  · exact u43759

def r44382 : Route 9 := (fun mask => (mask,id))

def c44382 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44382 : Upper (D 7) (R 7) [96,260,40] 13 := by
  apply FastRouting.sound _ _ [96,260,40] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r44382 c44382
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43760
  · exact u43761
  · exact u43762
  · exact u43763
  · exact u43764
  · exact u43765
  · exact u43766
  · exact u43767
  · exact u43768
  · exact u43769

def b44383 : PairBound 9 := { available := 155, camps := [{ cop := 0, region := 4, targets := 130 },{ cop := 2, region := 1, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 100 155 155 187 219 155 411), lower := (rows 97 262 100 8 16 32 64 128 256), losses := [] }

theorem u44383 : Upper (D 7) (R 7) [96,260,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r44384 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44384 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44384 : Upper (D 7) (R 7) [96,260,129] 13 := by
  apply FastRouting.sound _ _ [96,260,129] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r44384 c44384
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43770
  · exact u43771
  · exact u43772
  · exact u43773
  · exact u43774
  · exact u43775
  · exact u43776
  · exact u43777
  · exact u43778
  · exact u43779
  · exact u43780

def r44385 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44385 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44385 : Upper (D 7) (R 7) [96,260,130] 13 := by
  apply FastRouting.sound _ _ [96,260,130] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r44385 c44385
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43781
  · exact u43782
  · exact u43783
  · exact u43784
  · exact u43785
  · exact u43786
  · exact u43787
  · exact u43788
  · exact u43789
  · exact u43790
  · exact u43791

def r44386 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44386 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44386 : Upper (D 7) (R 7) [96,260,136] 13 := by
  apply FastRouting.sound _ _ [96,260,136] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r44386 c44386
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43792
  · exact u43793
  · exact u43794
  · exact u43795
  · exact u43796
  · exact u43797
  · exact u43798
  · exact u43799
  · exact u43800
  · exact u43801
  · exact u43802

def r44387 : Route 9 := (fun mask => (mask,id))

def c44387 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44387 : Upper (D 7) (R 7) [96,260,160] 13 := by
  apply FastRouting.sound _ _ [96,260,160] 13 (by decide) (choices 2) [3,17,18,65,66,80,129,130,144,192] r44387 c44387
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43803
  · exact u43804
  · exact u43805
  · exact u43806
  · exact u43807
  · exact u43808
  · exact u43809
  · exact u43810
  · exact u43811
  · exact u43812

def r44388 : Route 9 := (fun mask => (mask,id))

def c44388 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44388 : Upper (D 7) (R 7) [96,288,3] 13 := by
  apply FastRouting.sound _ _ [96,288,3] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44388 c44388
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43813
  · exact u43814
  · exact u43815
  · exact u43816
  · exact u43817
  · exact u43818
  · exact u43819
  · exact u43820
  · exact u43821
  · exact u43822
  · exact u43823
  · exact u43824
  · exact u43825
  · exact u43826
  · exact u43827

theorem m44389_3 : Upper (D 7) (R 7) [96,288,9,3] 13 :=
  permutation_upper _ _ _ [96,288,3,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43814

def r44389 : Route 9 := (fun mask => (mask,id))

def c44389 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44389 : Upper (D 7) (R 7) [96,288,9] 13 := by
  apply FastRouting.sound _ _ [96,288,9] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44389 c44389
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44389_3
  · exact u43828
  · exact u43829
  · exact u43830
  · exact u43831
  · exact u43832
  · exact u43833
  · exact u43834
  · exact u43835
  · exact u43836
  · exact u43837
  · exact u43838
  · exact u43839
  · exact u43840
  · exact u43841

theorem m44390_3 : Upper (D 7) (R 7) [96,288,10,3] 13 :=
  permutation_upper _ _ _ [96,288,3,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43815

theorem m44390_5 : Upper (D 7) (R 7) [96,288,10,5] 13 :=
  permutation_upper _ _ _ [96,288,9,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43829

def r44390 : Route 9 := (fun mask => (mask,id))

def c44390 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44390 : Upper (D 7) (R 7) [96,288,10] 13 := by
  apply FastRouting.sound _ _ [96,288,10] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44390 c44390
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44390_3
  · exact m44390_5
  · exact u43842
  · exact u43843
  · exact u43844
  · exact u43845
  · exact u43846
  · exact u43847
  · exact u43848
  · exact u43849
  · exact u43850
  · exact u43851
  · exact u43852
  · exact u43853
  · exact u43854

theorem m44391_3 : Upper (D 7) (R 7) [96,288,24,3] 13 :=
  permutation_upper _ _ _ [96,288,3,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43818

theorem m44391_5 : Upper (D 7) (R 7) [96,288,24,5] 13 :=
  permutation_upper _ _ _ [96,288,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43832

theorem m44391_6 : Upper (D 7) (R 7) [96,288,24,6] 13 :=
  permutation_upper _ _ _ [96,288,10,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43845

def r44391 : Route 9 := (fun mask => (mask,id))

def c44391 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 257 => 8 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 4 | 36 => 5 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44391 : Upper (D 7) (R 7) [96,288,24] 13 := by
  apply FastRouting.sound _ _ [96,288,24] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r44391 c44391
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44391_3
  · exact m44391_5
  · exact m44391_6
  · exact u43867
  · exact u43868
  · exact u43869
  · exact u43870
  · exact u43871
  · exact u43872
  · exact u43873

def b44392 : PairBound 9 := { available := 159, camps := [{ cop := 0, region := 4, targets := 162 },{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(2,7)], upper := (rows 97 290 69 159 159 191 223 159 415), lower := (rows 97 290 69 8 16 32 64 128 256), losses := [] }

theorem u44392 : Upper (D 7) (R 7) [96,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m44393_3 : Upper (D 7) (R 7) [96,288,66,3] 13 :=
  permutation_upper _ _ _ [96,288,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43820

theorem m44393_5 : Upper (D 7) (R 7) [96,288,66,5] 13 :=
  permutation_upper _ _ _ [96,288,9,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43834

theorem m44393_6 : Upper (D 7) (R 7) [96,288,66,6] 13 :=
  permutation_upper _ _ _ [96,288,10,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43847

theorem m44393_17 : Upper (D 7) (R 7) [96,288,66,17] 13 :=
  permutation_upper _ _ _ [96,288,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43855

theorem m44393_18 : Upper (D 7) (R 7) [96,288,66,18] 13 :=
  permutation_upper _ _ _ [96,288,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43861

theorem m44393_20 : Upper (D 7) (R 7) [96,288,66,20] 13 :=
  permutation_upper _ _ _ [96,288,24,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43868

def r44393 : Route 9 := (fun mask => (mask,id))

def c44393 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 48 => 5 | 80 => 6 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u44393 : Upper (D 7) (R 7) [96,288,66] 13 := by
  apply FastRouting.sound _ _ [96,288,66] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144] r44393 c44393
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44393_3
  · exact m44393_5
  · exact m44393_6
  · exact m44393_17
  · exact m44393_18
  · exact m44393_20
  · exact u43877
  · exact u43878
  · exact u43879
  · exact u43880

theorem m44394_3 : Upper (D 7) (R 7) [96,288,72,3] 13 :=
  permutation_upper _ _ _ [96,288,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43821

theorem m44394_5 : Upper (D 7) (R 7) [96,288,72,5] 13 :=
  permutation_upper _ _ _ [96,288,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43835

theorem m44394_6 : Upper (D 7) (R 7) [96,288,72,6] 13 :=
  permutation_upper _ _ _ [96,288,10,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43848

theorem m44394_17 : Upper (D 7) (R 7) [96,288,72,17] 13 :=
  permutation_upper _ _ _ [96,288,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43856

theorem m44394_18 : Upper (D 7) (R 7) [96,288,72,18] 13 :=
  permutation_upper _ _ _ [96,288,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43862

theorem m44394_20 : Upper (D 7) (R 7) [96,288,72,20] 13 :=
  permutation_upper _ _ _ [96,288,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43869

def r44394 : Route 9 := (fun mask => (mask,id))

def c44394 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 48 => 5 | 80 => 6 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u44394 : Upper (D 7) (R 7) [96,288,72] 13 := by
  apply FastRouting.sound _ _ [96,288,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144] r44394 c44394
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44394_3
  · exact m44394_5
  · exact m44394_6
  · exact m44394_17
  · exact m44394_18
  · exact m44394_20
  · exact u43881
  · exact u43882
  · exact u43883
  · exact u43884

theorem m44395_3 : Upper (D 7) (R 7) [96,288,129,3] 13 :=
  permutation_upper _ _ _ [96,288,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43823

theorem m44395_5 : Upper (D 7) (R 7) [96,288,129,5] 13 :=
  permutation_upper _ _ _ [96,288,9,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43837

theorem m44395_6 : Upper (D 7) (R 7) [96,288,129,6] 13 :=
  permutation_upper _ _ _ [96,288,10,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43850

theorem m44395_17 : Upper (D 7) (R 7) [96,288,129,17] 13 :=
  permutation_upper _ _ _ [96,288,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43857

theorem m44395_18 : Upper (D 7) (R 7) [96,288,129,18] 13 :=
  permutation_upper _ _ _ [96,288,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43863

theorem m44395_20 : Upper (D 7) (R 7) [96,288,129,20] 13 :=
  permutation_upper _ _ _ [96,288,24,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43870

theorem m44395_65 : Upper (D 7) (R 7) [96,288,129,65] 13 :=
  permutation_upper _ _ _ [96,288,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43874

theorem m44395_66 : Upper (D 7) (R 7) [96,288,129,66] 13 :=
  permutation_upper _ _ _ [96,288,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43877

theorem m44395_68 : Upper (D 7) (R 7) [96,288,129,68] 13 :=
  permutation_upper _ _ _ [96,288,72,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43881

theorem m44395_80 : Upper (D 7) (R 7) [96,288,129,80] 13 :=
  permutation_upper _ _ _ [96,288,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43885

def r44395 : Route 9 := (fun mask => (mask,id))

def c44395 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44395 : Upper (D 7) (R 7) [96,288,129] 13 := by
  apply FastRouting.sound _ _ [96,288,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44395 c44395
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44395_3
  · exact m44395_5
  · exact m44395_6
  · exact m44395_17
  · exact m44395_18
  · exact m44395_20
  · exact m44395_65
  · exact m44395_66
  · exact m44395_68
  · exact m44395_80
  · exact u43888
  · exact u43889
  · exact u43890
  · exact u43891
  · exact u43892

theorem m44396_3 : Upper (D 7) (R 7) [96,288,130,3] 13 :=
  permutation_upper _ _ _ [96,288,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43824

theorem m44396_5 : Upper (D 7) (R 7) [96,288,130,5] 13 :=
  permutation_upper _ _ _ [96,288,9,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43838

theorem m44396_6 : Upper (D 7) (R 7) [96,288,130,6] 13 :=
  permutation_upper _ _ _ [96,288,10,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43851

theorem m44396_17 : Upper (D 7) (R 7) [96,288,130,17] 13 :=
  permutation_upper _ _ _ [96,288,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43858

theorem m44396_18 : Upper (D 7) (R 7) [96,288,130,18] 13 :=
  permutation_upper _ _ _ [96,288,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43864

theorem m44396_20 : Upper (D 7) (R 7) [96,288,130,20] 13 :=
  permutation_upper _ _ _ [96,288,24,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43871

theorem m44396_65 : Upper (D 7) (R 7) [96,288,130,65] 13 :=
  permutation_upper _ _ _ [96,288,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43875

theorem m44396_66 : Upper (D 7) (R 7) [96,288,130,66] 13 :=
  permutation_upper _ _ _ [96,288,66,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43878

theorem m44396_68 : Upper (D 7) (R 7) [96,288,130,68] 13 :=
  permutation_upper _ _ _ [96,288,72,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43882

theorem m44396_80 : Upper (D 7) (R 7) [96,288,130,80] 13 :=
  permutation_upper _ _ _ [96,288,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43886

theorem m44396_129 : Upper (D 7) (R 7) [96,288,130,129] 13 :=
  permutation_upper _ _ _ [96,288,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43889

def r44396 : Route 9 := (fun mask => (mask,id))

def c44396 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44396 : Upper (D 7) (R 7) [96,288,130] 13 := by
  apply FastRouting.sound _ _ [96,288,130] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44396 c44396
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44396_3
  · exact m44396_5
  · exact m44396_6
  · exact m44396_17
  · exact m44396_18
  · exact m44396_20
  · exact m44396_65
  · exact m44396_66
  · exact m44396_68
  · exact m44396_80
  · exact m44396_129
  · exact u43893
  · exact u43894
  · exact u43895
  · exact u43896

theorem m44397_3 : Upper (D 7) (R 7) [96,288,136,3] 13 :=
  permutation_upper _ _ _ [96,288,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43825

theorem m44397_5 : Upper (D 7) (R 7) [96,288,136,5] 13 :=
  permutation_upper _ _ _ [96,288,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43839

theorem m44397_6 : Upper (D 7) (R 7) [96,288,136,6] 13 :=
  permutation_upper _ _ _ [96,288,10,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43852

theorem m44397_17 : Upper (D 7) (R 7) [96,288,136,17] 13 :=
  permutation_upper _ _ _ [96,288,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43859

theorem m44397_18 : Upper (D 7) (R 7) [96,288,136,18] 13 :=
  permutation_upper _ _ _ [96,288,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43865

theorem m44397_20 : Upper (D 7) (R 7) [96,288,136,20] 13 :=
  permutation_upper _ _ _ [96,288,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43872

theorem m44397_65 : Upper (D 7) (R 7) [96,288,136,65] 13 :=
  permutation_upper _ _ _ [96,288,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43876

theorem m44397_66 : Upper (D 7) (R 7) [96,288,136,66] 13 :=
  permutation_upper _ _ _ [96,288,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43879

theorem m44397_68 : Upper (D 7) (R 7) [96,288,136,68] 13 :=
  permutation_upper _ _ _ [96,288,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43883

theorem m44397_80 : Upper (D 7) (R 7) [96,288,136,80] 13 :=
  permutation_upper _ _ _ [96,288,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43887

theorem m44397_129 : Upper (D 7) (R 7) [96,288,136,129] 13 :=
  permutation_upper _ _ _ [96,288,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43890

theorem m44397_130 : Upper (D 7) (R 7) [96,288,136,130] 13 :=
  permutation_upper _ _ _ [96,288,130,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43894

def r44397 : Route 9 := (fun mask => (mask,id))

def c44397 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44397 : Upper (D 7) (R 7) [96,288,136] 13 := by
  apply FastRouting.sound _ _ [96,288,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r44397 c44397
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44397_3
  · exact m44397_5
  · exact m44397_6
  · exact m44397_17
  · exact m44397_18
  · exact m44397_20
  · exact m44397_65
  · exact m44397_66
  · exact m44397_68
  · exact m44397_80
  · exact m44397_129
  · exact m44397_130
  · exact u43897
  · exact u43898
  · exact u43899

theorem m44398_3 : Upper (D 7) (R 7) [96,288,192,3] 13 :=
  permutation_upper _ _ _ [96,288,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43827

theorem m44398_5 : Upper (D 7) (R 7) [96,288,192,5] 13 :=
  permutation_upper _ _ _ [96,288,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43841

theorem m44398_6 : Upper (D 7) (R 7) [96,288,192,6] 13 :=
  permutation_upper _ _ _ [96,288,10,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43854

theorem m44398_17 : Upper (D 7) (R 7) [96,288,192,17] 13 :=
  permutation_upper _ _ _ [96,288,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43860

theorem m44398_18 : Upper (D 7) (R 7) [96,288,192,18] 13 :=
  permutation_upper _ _ _ [96,288,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43866

theorem m44398_20 : Upper (D 7) (R 7) [96,288,192,20] 13 :=
  permutation_upper _ _ _ [96,288,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43873

theorem m44398_129 : Upper (D 7) (R 7) [96,288,192,129] 13 :=
  permutation_upper _ _ _ [96,288,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43892

theorem m44398_130 : Upper (D 7) (R 7) [96,288,192,130] 13 :=
  permutation_upper _ _ _ [96,288,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43896

theorem m44398_132 : Upper (D 7) (R 7) [96,288,192,132] 13 :=
  permutation_upper _ _ _ [96,288,136,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43899

theorem m44398_144 : Upper (D 7) (R 7) [96,288,192,144] 13 :=
  permutation_upper _ _ _ [96,288,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u43900

def r44398 : Route 9 := (fun mask => (mask,id))

def c44398 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 48 => 5 | 80 => 6 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u44398 : Upper (D 7) (R 7) [96,288,192] 13 := by
  apply FastRouting.sound _ _ [96,288,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144] r44398 c44398
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m44398_3
  · exact m44398_5
  · exact m44398_6
  · exact m44398_17
  · exact m44398_18
  · exact m44398_20
  · exact m44398_129
  · exact m44398_130
  · exact m44398_132
  · exact m44398_144

def r44399 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c44399 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u44399 : Upper (D 7) (R 7) [96,384,3] 13 := by
  apply FastRouting.sound _ _ [96,384,3] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,129,130,132,144,160] r44399 c44399
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u43901
  · exact u43902
  · exact u43903
  · exact u43904
  · exact u43905
  · exact u43906
  · exact u43907
  · exact u43908
  · exact u43909
  · exact u43910
  · exact u43911
  · exact u43912
  · exact u43913
  · exact u43914
  · exact u43915
  · exact u43916

#print axioms u44399
end Delivery.IrregularNine14.P07
