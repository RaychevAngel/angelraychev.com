import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0573
import IrregularNine14P07C0574
import IrregularNine14P07C0575
import IrregularNine14P07C0576
import IrregularNine14P07C0577
import IrregularNine14P07C0578

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r42120 : Route 9 := (fun mask => (mask,id))

def c42120 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42120 : Upper (D 7) (R 7) [34,68,40,144] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42120 c42120
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34417
  · exact u34418
  · exact u34419
  · exact u34420
  · exact u34421
  · exact u34422
  · exact u34423
  · exact u34424
  · exact u34425
  · exact u34426

def b42121 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 44 200 403 435 467 403 403), lower := (rows 35 70 44 200 16 32 64 128 256), losses := [] }

theorem u42121 : Upper (D 7) (R 7) [34,68,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42122 : Route 9 := (fun mask => (mask,id))

def c42122 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42122 : Upper (D 7) (R 7) [34,68,40,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42122 c42122
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34427
  · exact u34428
  · exact u34429
  · exact u34430
  · exact u34431
  · exact u34432

def r42123 : Route 9 := (fun mask => (mask,id))

def c42123 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42123 : Upper (D 7) (R 7) [34,68,40,258] 13 := by
  apply FastRouting.sound _ _ [34,68,40,258] 13 (by decide) (choices 2) [65,129,192] r42123 c42123
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u34433
  · exact u34434
  · exact u34435

def r42124 : Route 9 := (fun mask => (mask,id))

def c42124 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42124 : Upper (D 7) (R 7) [34,68,40,272] 13 := by
  apply FastRouting.sound _ _ [34,68,40,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42124 c42124
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34436
  · exact u34437
  · exact u34438
  · exact u34439
  · exact u34440
  · exact u34441

def b42125 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(3,5),(4,5),(4,6)], upper := (rows 35 70 44 328 147 179 211 147 403), lower := (rows 35 70 44 328 16 32 64 128 256), losses := [] }

theorem u42125 : Upper (D 7) (R 7) [34,68,40,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42126 : Route 9 := (fun mask => (mask,id))

def c42126 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42126 : Upper (D 7) (R 7) [34,68,40,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42126 c42126
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34442
  · exact u34443
  · exact u34444
  · exact u34445
  · exact u34446
  · exact u34447

def b42127 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 11 504 504 504 504 504), lower := (rows 35 70 133 11 16 32 64 128 256), losses := [] }

theorem u42127 : Upper (D 7) (R 7) [34,68,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42128 : Route 9 := (fun mask => (mask,id))

def c42128 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u42128 : Upper (D 7) (R 7) [34,68,129,17] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192,258,264,288,320,384] r42128 c42128
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34458
  · exact u34459
  · exact u34460
  · exact u34461
  · exact u34462
  · exact u34463
  · exact u34464
  · exact u34465
  · exact u34466
  · exact u34467
  · exact u34468
  · exact u34469
  · exact u34470
  · exact u34471
  · exact u34472

theorem m42129_9 : Upper (D 7) (R 7) [34,68,129,18,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34458

def r42129 : Route 9 := (fun mask => (mask,id))

def c42129 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u42129 : Upper (D 7) (R 7) [34,68,129,18] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r42129 c42129
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42129_9
  · exact u34473
  · exact u34474
  · exact u34475
  · exact u34476
  · exact u34477
  · exact u34478
  · exact u34479
  · exact u34480
  · exact u34481
  · exact u34482
  · exact u34483
  · exact u34484
  · exact u34485
  · exact u34486

def b42130 : PairBound 9 := { available := 474, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 133 41 474 506 474 474 474), lower := (rows 35 70 133 41 16 32 64 128 256), losses := [] }

theorem u42130 : Upper (D 7) (R 7) [34,68,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42131 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 133 42 473 505 473 473 473), lower := (rows 35 70 133 42 16 32 64 128 256), losses := [] }

theorem u42131 : Upper (D 7) (R 7) [34,68,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42132_3 : Upper (D 7) (R 7) [34,68,129,48,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34448

theorem m42132_9 : Upper (D 7) (R 7) [34,68,129,48,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34460

theorem m42132_10 : Upper (D 7) (R 7) [34,68,129,48,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34474

def r42132 : Route 9 := (fun mask => (mask,id))

def c42132 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42132 : Upper (D 7) (R 7) [34,68,129,48] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,257,258,264,320,384] r42132 c42132
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42132_3
  · exact m42132_9
  · exact m42132_10
  · exact u34503
  · exact u34504
  · exact u34505
  · exact u34506
  · exact u34507
  · exact u34508
  · exact u34509
  · exact u34510
  · exact u34511
  · exact u34512
  · exact u34513
  · exact u34514

theorem m42133_10 : Upper (D 7) (R 7) [34,68,129,65,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34475

theorem m42133_34 : Upper (D 7) (R 7) [34,68,129,65,34] 13 :=
  permutation_upper _ _ _ [34,68,129,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34495

theorem m42133_40 : Upper (D 7) (R 7) [34,68,129,65,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34503

def r42133 : Route 9 := (fun mask => (mask,id))

def c42133 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42133 : Upper (D 7) (R 7) [34,68,129,65] 13 := by
  apply FastRouting.sound _ _ [34,68,129,65] 13 (by decide) (choices 2) [10,34,40,130,136,160,258,264,288,384] r42133 c42133
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42133_10
  · exact m42133_34
  · exact m42133_40
  · exact u34515
  · exact u34516
  · exact u34517
  · exact u34518
  · exact u34519
  · exact u34520
  · exact u34521

def b42134 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 133 74 441 441 505 441 441), lower := (rows 35 70 133 74 16 32 64 128 256), losses := [] }

theorem u42134 : Upper (D 7) (R 7) [34,68,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42135_3 : Upper (D 7) (R 7) [34,68,129,80,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34449

theorem m42135_9 : Upper (D 7) (R 7) [34,68,129,80,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34462

theorem m42135_10 : Upper (D 7) (R 7) [34,68,129,80,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34476

theorem m42135_33 : Upper (D 7) (R 7) [34,68,129,80,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34487

theorem m42135_34 : Upper (D 7) (R 7) [34,68,129,80,34] 13 :=
  permutation_upper _ _ _ [34,68,129,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34496

theorem m42135_40 : Upper (D 7) (R 7) [34,68,129,80,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34505

def r42135 : Route 9 := (fun mask => (mask,id))

def c42135 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42135 : Upper (D 7) (R 7) [34,68,129,80] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,257,258,264,288,384] r42135 c42135
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42135_3
  · exact m42135_9
  · exact m42135_10
  · exact m42135_33
  · exact m42135_34
  · exact m42135_40
  · exact u34528
  · exact u34529
  · exact u34530
  · exact u34531
  · exact u34532
  · exact u34533
  · exact u34534
  · exact u34535
  · exact u34536

theorem m42136_3 : Upper (D 7) (R 7) [34,68,129,96,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34450

theorem m42136_9 : Upper (D 7) (R 7) [34,68,129,96,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34463

theorem m42136_10 : Upper (D 7) (R 7) [34,68,129,96,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34477

def r42136 : Route 9 := (fun mask => (mask,id))

def c42136 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42136 : Upper (D 7) (R 7) [34,68,129,96] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r42136 c42136
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42136_3
  · exact m42136_9
  · exact m42136_10
  · exact u34537
  · exact u34538
  · exact u34539
  · exact u34540
  · exact u34541
  · exact u34542
  · exact u34543

def b42137 : PairBound 9 := { available := 378, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 35 70 133 137 378 378 378 506 378), lower := (rows 35 70 133 137 16 32 64 128 256), losses := [] }

theorem u42137 : Upper (D 7) (R 7) [34,68,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42138_9 : Upper (D 7) (R 7) [34,68,129,130,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34464

theorem m42138_33 : Upper (D 7) (R 7) [34,68,129,130,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34488

theorem m42138_40 : Upper (D 7) (R 7) [34,68,129,130,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34507

theorem m42138_65 : Upper (D 7) (R 7) [34,68,129,130,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34515

theorem m42138_72 : Upper (D 7) (R 7) [34,68,129,130,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34529

theorem m42138_96 : Upper (D 7) (R 7) [34,68,129,130,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34538

def r42138 : Route 9 := (fun mask => (mask,id))

def c42138 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42138 : Upper (D 7) (R 7) [34,68,129,130] 13 := by
  apply FastRouting.sound _ _ [34,68,129,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r42138 c42138
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42138_9
  · exact m42138_33
  · exact m42138_40
  · exact m42138_65
  · exact m42138_72
  · exact m42138_96
  · exact u34548
  · exact u34549
  · exact u34550
  · exact u34551

theorem m42139_3 : Upper (D 7) (R 7) [34,68,129,144,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34451

theorem m42139_9 : Upper (D 7) (R 7) [34,68,129,144,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34465

theorem m42139_10 : Upper (D 7) (R 7) [34,68,129,144,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34479

theorem m42139_33 : Upper (D 7) (R 7) [34,68,129,144,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34489

theorem m42139_34 : Upper (D 7) (R 7) [34,68,129,144,34] 13 :=
  permutation_upper _ _ _ [34,68,129,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34497

theorem m42139_40 : Upper (D 7) (R 7) [34,68,129,144,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34508

theorem m42139_65 : Upper (D 7) (R 7) [34,68,129,144,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34516

theorem m42139_66 : Upper (D 7) (R 7) [34,68,129,144,66] 13 :=
  permutation_upper _ _ _ [34,68,129,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34522

theorem m42139_72 : Upper (D 7) (R 7) [34,68,129,144,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34530

theorem m42139_96 : Upper (D 7) (R 7) [34,68,129,144,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34539

def r42139 : Route 9 := (fun mask => (mask,id))

def c42139 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42139 : Upper (D 7) (R 7) [34,68,129,144] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,257,258,264,288,320] r42139 c42139
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42139_3
  · exact m42139_9
  · exact m42139_10
  · exact m42139_33
  · exact m42139_34
  · exact m42139_40
  · exact m42139_65
  · exact m42139_66
  · exact m42139_72
  · exact m42139_96
  · exact u34552
  · exact u34553
  · exact u34554
  · exact u34555
  · exact u34556

theorem m42140_3 : Upper (D 7) (R 7) [34,68,129,160,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34452

theorem m42140_9 : Upper (D 7) (R 7) [34,68,129,160,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34466

theorem m42140_10 : Upper (D 7) (R 7) [34,68,129,160,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34480

theorem m42140_65 : Upper (D 7) (R 7) [34,68,129,160,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34517

theorem m42140_66 : Upper (D 7) (R 7) [34,68,129,160,66] 13 :=
  permutation_upper _ _ _ [34,68,129,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34523

theorem m42140_72 : Upper (D 7) (R 7) [34,68,129,160,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34531

def r42140 : Route 9 := (fun mask => (mask,id))

def c42140 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42140 : Upper (D 7) (R 7) [34,68,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r42140 c42140
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42140_3
  · exact m42140_9
  · exact m42140_10
  · exact m42140_65
  · exact m42140_66
  · exact m42140_72
  · exact u34557
  · exact u34558
  · exact u34559
  · exact u34560

theorem m42141_3 : Upper (D 7) (R 7) [34,68,129,192,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34453

theorem m42141_9 : Upper (D 7) (R 7) [34,68,129,192,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34467

theorem m42141_10 : Upper (D 7) (R 7) [34,68,129,192,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34481

theorem m42141_33 : Upper (D 7) (R 7) [34,68,129,192,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34490

theorem m42141_34 : Upper (D 7) (R 7) [34,68,129,192,34] 13 :=
  permutation_upper _ _ _ [34,68,129,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34498

theorem m42141_40 : Upper (D 7) (R 7) [34,68,129,192,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34509

def r42141 : Route 9 := (fun mask => (mask,id))

def c42141 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42141 : Upper (D 7) (R 7) [34,68,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r42141 c42141
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42141_3
  · exact m42141_9
  · exact m42141_10
  · exact m42141_33
  · exact m42141_34
  · exact m42141_40
  · exact u34561
  · exact u34562
  · exact u34563
  · exact u34564

theorem m42142_10 : Upper (D 7) (R 7) [34,68,129,257,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34482

theorem m42142_34 : Upper (D 7) (R 7) [34,68,129,257,34] 13 :=
  permutation_upper _ _ _ [34,68,129,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34499

theorem m42142_40 : Upper (D 7) (R 7) [34,68,129,257,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34510

theorem m42142_66 : Upper (D 7) (R 7) [34,68,129,257,66] 13 :=
  permutation_upper _ _ _ [34,68,129,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34524

theorem m42142_72 : Upper (D 7) (R 7) [34,68,129,257,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34532

theorem m42142_96 : Upper (D 7) (R 7) [34,68,129,257,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34540

theorem m42142_130 : Upper (D 7) (R 7) [34,68,129,257,130] 13 :=
  permutation_upper _ _ _ [34,68,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34548

theorem m42142_136 : Upper (D 7) (R 7) [34,68,129,257,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34552

theorem m42142_160 : Upper (D 7) (R 7) [34,68,129,257,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34557

theorem m42142_192 : Upper (D 7) (R 7) [34,68,129,257,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34561

def r42142 : Route 9 := (fun mask => (mask,id))

def c42142 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42142 : Upper (D 7) (R 7) [34,68,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r42142 c42142
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42142_10
  · exact m42142_34
  · exact m42142_40
  · exact m42142_66
  · exact m42142_72
  · exact m42142_96
  · exact m42142_130
  · exact m42142_136
  · exact m42142_160
  · exact m42142_192

theorem m42143_9 : Upper (D 7) (R 7) [34,68,129,258,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34468

theorem m42143_33 : Upper (D 7) (R 7) [34,68,129,258,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34491

theorem m42143_40 : Upper (D 7) (R 7) [34,68,129,258,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34511

theorem m42143_65 : Upper (D 7) (R 7) [34,68,129,258,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34518

theorem m42143_72 : Upper (D 7) (R 7) [34,68,129,258,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34533

theorem m42143_96 : Upper (D 7) (R 7) [34,68,129,258,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34541

theorem m42143_129 : Upper (D 7) (R 7) [34,68,129,258,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34544

theorem m42143_136 : Upper (D 7) (R 7) [34,68,129,258,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34553

theorem m42143_160 : Upper (D 7) (R 7) [34,68,129,258,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34558

theorem m42143_192 : Upper (D 7) (R 7) [34,68,129,258,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34562

def r42143 : Route 9 := (fun mask => (mask,id))

def c42143 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42143 : Upper (D 7) (R 7) [34,68,129,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,258] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r42143 c42143
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42143_9
  · exact m42143_33
  · exact m42143_40
  · exact m42143_65
  · exact m42143_72
  · exact m42143_96
  · exact m42143_129
  · exact m42143_136
  · exact m42143_160
  · exact m42143_192

theorem m42144_3 : Upper (D 7) (R 7) [34,68,129,272,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34454

theorem m42144_9 : Upper (D 7) (R 7) [34,68,129,272,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34469

theorem m42144_10 : Upper (D 7) (R 7) [34,68,129,272,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34483

theorem m42144_33 : Upper (D 7) (R 7) [34,68,129,272,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34492

theorem m42144_34 : Upper (D 7) (R 7) [34,68,129,272,34] 13 :=
  permutation_upper _ _ _ [34,68,129,34,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34500

theorem m42144_40 : Upper (D 7) (R 7) [34,68,129,272,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34512

theorem m42144_65 : Upper (D 7) (R 7) [34,68,129,272,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34519

theorem m42144_66 : Upper (D 7) (R 7) [34,68,129,272,66] 13 :=
  permutation_upper _ _ _ [34,68,129,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34525

theorem m42144_72 : Upper (D 7) (R 7) [34,68,129,272,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34534

theorem m42144_96 : Upper (D 7) (R 7) [34,68,129,272,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34542

theorem m42144_129 : Upper (D 7) (R 7) [34,68,129,272,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34545

theorem m42144_130 : Upper (D 7) (R 7) [34,68,129,272,130] 13 :=
  permutation_upper _ _ _ [34,68,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34549

theorem m42144_136 : Upper (D 7) (R 7) [34,68,129,272,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34554

theorem m42144_160 : Upper (D 7) (R 7) [34,68,129,272,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34559

theorem m42144_192 : Upper (D 7) (R 7) [34,68,129,272,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34563

def r42144 : Route 9 := (fun mask => (mask,id))

def c42144 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42144 : Upper (D 7) (R 7) [34,68,129,272] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r42144 c42144
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42144_3
  · exact m42144_9
  · exact m42144_10
  · exact m42144_33
  · exact m42144_34
  · exact m42144_40
  · exact m42144_65
  · exact m42144_66
  · exact m42144_72
  · exact m42144_96
  · exact m42144_129
  · exact m42144_130
  · exact m42144_136
  · exact m42144_160
  · exact m42144_192

theorem m42145_3 : Upper (D 7) (R 7) [34,68,129,288,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34455

theorem m42145_9 : Upper (D 7) (R 7) [34,68,129,288,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34470

theorem m42145_10 : Upper (D 7) (R 7) [34,68,129,288,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34484

theorem m42145_65 : Upper (D 7) (R 7) [34,68,129,288,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34520

theorem m42145_66 : Upper (D 7) (R 7) [34,68,129,288,66] 13 :=
  permutation_upper _ _ _ [34,68,129,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34526

theorem m42145_72 : Upper (D 7) (R 7) [34,68,129,288,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34535

theorem m42145_129 : Upper (D 7) (R 7) [34,68,129,288,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34546

theorem m42145_130 : Upper (D 7) (R 7) [34,68,129,288,130] 13 :=
  permutation_upper _ _ _ [34,68,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34550

theorem m42145_136 : Upper (D 7) (R 7) [34,68,129,288,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34555

theorem m42145_192 : Upper (D 7) (R 7) [34,68,129,288,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34564

def r42145 : Route 9 := (fun mask => (mask,id))

def c42145 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42145 : Upper (D 7) (R 7) [34,68,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,288] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42145 c42145
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42145_3
  · exact m42145_9
  · exact m42145_10
  · exact m42145_65
  · exact m42145_66
  · exact m42145_72
  · exact m42145_129
  · exact m42145_130
  · exact m42145_136
  · exact m42145_192

theorem m42146_3 : Upper (D 7) (R 7) [34,68,129,320,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34456

theorem m42146_9 : Upper (D 7) (R 7) [34,68,129,320,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34471

theorem m42146_10 : Upper (D 7) (R 7) [34,68,129,320,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34485

theorem m42146_33 : Upper (D 7) (R 7) [34,68,129,320,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34493

theorem m42146_34 : Upper (D 7) (R 7) [34,68,129,320,34] 13 :=
  permutation_upper _ _ _ [34,68,129,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34501

theorem m42146_40 : Upper (D 7) (R 7) [34,68,129,320,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34513

theorem m42146_129 : Upper (D 7) (R 7) [34,68,129,320,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34547

theorem m42146_130 : Upper (D 7) (R 7) [34,68,129,320,130] 13 :=
  permutation_upper _ _ _ [34,68,129,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34551

theorem m42146_136 : Upper (D 7) (R 7) [34,68,129,320,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34556

theorem m42146_160 : Upper (D 7) (R 7) [34,68,129,320,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34560

def r42146 : Route 9 := (fun mask => (mask,id))

def c42146 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42146 : Upper (D 7) (R 7) [34,68,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,320] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r42146 c42146
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42146_3
  · exact m42146_9
  · exact m42146_10
  · exact m42146_33
  · exact m42146_34
  · exact m42146_40
  · exact m42146_129
  · exact m42146_130
  · exact m42146_136
  · exact m42146_160

theorem m42147_3 : Upper (D 7) (R 7) [34,68,129,384,3] 13 :=
  permutation_upper _ _ _ [34,68,129,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34457

theorem m42147_9 : Upper (D 7) (R 7) [34,68,129,384,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34472

theorem m42147_10 : Upper (D 7) (R 7) [34,68,129,384,10] 13 :=
  permutation_upper _ _ _ [34,68,129,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34486

theorem m42147_33 : Upper (D 7) (R 7) [34,68,129,384,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34494

theorem m42147_34 : Upper (D 7) (R 7) [34,68,129,384,34] 13 :=
  permutation_upper _ _ _ [34,68,129,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34502

theorem m42147_40 : Upper (D 7) (R 7) [34,68,129,384,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34514

theorem m42147_65 : Upper (D 7) (R 7) [34,68,129,384,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34521

theorem m42147_66 : Upper (D 7) (R 7) [34,68,129,384,66] 13 :=
  permutation_upper _ _ _ [34,68,129,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34527

theorem m42147_72 : Upper (D 7) (R 7) [34,68,129,384,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34536

theorem m42147_96 : Upper (D 7) (R 7) [34,68,129,384,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34543

def r42147 : Route 9 := (fun mask => (mask,id))

def c42147 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42147 : Upper (D 7) (R 7) [34,68,129,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,384] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r42147 c42147
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42147_3
  · exact m42147_9
  · exact m42147_10
  · exact m42147_33
  · exact m42147_34
  · exact m42147_40
  · exact m42147_65
  · exact m42147_66
  · exact m42147_72
  · exact m42147_96

def r42148 : Route 9 := (fun mask => (mask,id))

def c42148 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u42148 : Upper (D 7) (R 7) [34,68,130,17] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r42148 c42148
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34565
  · exact u34566
  · exact u34567
  · exact u34568
  · exact u34569
  · exact u34570
  · exact u34571
  · exact u34572
  · exact u34573
  · exact u34574
  · exact u34575
  · exact u34576
  · exact u34577
  · exact u34578
  · exact u34579

def b42149 : PairBound 9 := { available := 473, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 134 41 473 505 473 473 473), lower := (rows 35 70 134 41 16 32 64 128 256), losses := [] }

theorem u42149 : Upper (D 7) (R 7) [34,68,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42150_9 : Upper (D 7) (R 7) [34,68,130,48,9] 13 :=
  permutation_upper _ _ _ [34,68,130,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34567

def r42150 : Route 9 := (fun mask => (mask,id))

def c42150 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42150 : Upper (D 7) (R 7) [34,68,130,48] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r42150 c42150
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42150_9
  · exact u34588
  · exact u34589
  · exact u34590
  · exact u34591
  · exact u34592
  · exact u34593
  · exact u34594
  · exact u34595
  · exact u34596

theorem m42151_9 : Upper (D 7) (R 7) [34,68,130,65,9] 13 :=
  permutation_upper _ _ _ [34,68,130,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34568

theorem m42151_33 : Upper (D 7) (R 7) [34,68,130,65,33] 13 :=
  permutation_upper _ _ _ [34,68,130,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34580

theorem m42151_40 : Upper (D 7) (R 7) [34,68,130,65,40] 13 :=
  permutation_upper _ _ _ [34,68,130,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34588

def r42151 : Route 9 := (fun mask => (mask,id))

def c42151 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42151 : Upper (D 7) (R 7) [34,68,130,65] 13 := by
  apply FastRouting.sound _ _ [34,68,130,65] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r42151 c42151
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42151_9
  · exact m42151_33
  · exact m42151_40
  · exact u34597
  · exact u34598
  · exact u34599
  · exact u34600
  · exact u34601
  · exact u34602
  · exact u34603

theorem m42152_9 : Upper (D 7) (R 7) [34,68,130,80,9] 13 :=
  permutation_upper _ _ _ [34,68,130,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34569

theorem m42152_33 : Upper (D 7) (R 7) [34,68,130,80,33] 13 :=
  permutation_upper _ _ _ [34,68,130,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34581

theorem m42152_40 : Upper (D 7) (R 7) [34,68,130,80,40] 13 :=
  permutation_upper _ _ _ [34,68,130,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34589

def r42152 : Route 9 := (fun mask => (mask,id))

def c42152 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42152 : Upper (D 7) (R 7) [34,68,130,80] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r42152 c42152
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42152_9
  · exact m42152_33
  · exact m42152_40
  · exact u34604
  · exact u34605
  · exact u34606
  · exact u34607
  · exact u34608
  · exact u34609
  · exact u34610

theorem m42153_9 : Upper (D 7) (R 7) [34,68,130,96,9] 13 :=
  permutation_upper _ _ _ [34,68,130,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34570

def r42153 : Route 9 := (fun mask => (mask,id))

def c42153 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42153 : Upper (D 7) (R 7) [34,68,130,96] 13 := by
  apply FastRouting.sound _ _ [34,68,130,96] 13 (by decide) (choices 2) [9,129,136,257,264,384] r42153 c42153
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42153_9
  · exact u34611
  · exact u34612
  · exact u34613
  · exact u34614
  · exact u34615

theorem m42154_9 : Upper (D 7) (R 7) [34,68,130,129,9] 13 :=
  permutation_upper _ _ _ [34,68,130,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34571

theorem m42154_33 : Upper (D 7) (R 7) [34,68,130,129,33] 13 :=
  permutation_upper _ _ _ [34,68,130,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34582

theorem m42154_40 : Upper (D 7) (R 7) [34,68,130,129,40] 13 :=
  permutation_upper _ _ _ [34,68,130,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34590

theorem m42154_65 : Upper (D 7) (R 7) [34,68,130,129,65] 13 :=
  permutation_upper _ _ _ [34,68,130,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34597

theorem m42154_72 : Upper (D 7) (R 7) [34,68,130,129,72] 13 :=
  permutation_upper _ _ _ [34,68,130,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34604

theorem m42154_96 : Upper (D 7) (R 7) [34,68,130,129,96] 13 :=
  permutation_upper _ _ _ [34,68,130,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34611

def r42154 : Route 9 := (fun mask => (mask,id))

def c42154 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42154 : Upper (D 7) (R 7) [34,68,130,129] 13 := by
  apply FastRouting.sound _ _ [34,68,130,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r42154 c42154
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42154_9
  · exact m42154_33
  · exact m42154_40
  · exact m42154_65
  · exact m42154_72
  · exact m42154_96
  · exact u34616
  · exact u34617
  · exact u34618
  · exact u34619

theorem m42155_9 : Upper (D 7) (R 7) [34,68,130,144,9] 13 :=
  permutation_upper _ _ _ [34,68,130,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34572

theorem m42155_33 : Upper (D 7) (R 7) [34,68,130,144,33] 13 :=
  permutation_upper _ _ _ [34,68,130,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34583

theorem m42155_40 : Upper (D 7) (R 7) [34,68,130,144,40] 13 :=
  permutation_upper _ _ _ [34,68,130,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34591

theorem m42155_65 : Upper (D 7) (R 7) [34,68,130,144,65] 13 :=
  permutation_upper _ _ _ [34,68,130,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34598

theorem m42155_72 : Upper (D 7) (R 7) [34,68,130,144,72] 13 :=
  permutation_upper _ _ _ [34,68,130,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34605

theorem m42155_96 : Upper (D 7) (R 7) [34,68,130,144,96] 13 :=
  permutation_upper _ _ _ [34,68,130,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34612

def r42155 : Route 9 := (fun mask => (mask,id))

def c42155 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42155 : Upper (D 7) (R 7) [34,68,130,144] 13 := by
  apply FastRouting.sound _ _ [34,68,130,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r42155 c42155
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42155_9
  · exact m42155_33
  · exact m42155_40
  · exact m42155_65
  · exact m42155_72
  · exact m42155_96
  · exact u34620
  · exact u34621
  · exact u34622
  · exact u34623

theorem m42156_9 : Upper (D 7) (R 7) [34,68,130,160,9] 13 :=
  permutation_upper _ _ _ [34,68,130,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34573

theorem m42156_65 : Upper (D 7) (R 7) [34,68,130,160,65] 13 :=
  permutation_upper _ _ _ [34,68,130,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34599

theorem m42156_72 : Upper (D 7) (R 7) [34,68,130,160,72] 13 :=
  permutation_upper _ _ _ [34,68,130,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34606

def r42156 : Route 9 := (fun mask => (mask,id))

def c42156 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42156 : Upper (D 7) (R 7) [34,68,130,160] 13 := by
  apply FastRouting.sound _ _ [34,68,130,160] 13 (by decide) (choices 2) [9,65,72,257,264,320] r42156 c42156
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42156_9
  · exact m42156_65
  · exact m42156_72
  · exact u34624
  · exact u34625
  · exact u34626

def b42157 : PairBound 9 := { available := 313, camps := [{ cop := 3, region := 6, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 134 200 313 313 377 441 313), lower := (rows 35 70 134 200 16 32 64 128 256), losses := [] }

theorem u42157 : Upper (D 7) (R 7) [34,68,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42158_9 : Upper (D 7) (R 7) [34,68,130,257,9] 13 :=
  permutation_upper _ _ _ [34,68,130,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34575

theorem m42158_33 : Upper (D 7) (R 7) [34,68,130,257,33] 13 :=
  permutation_upper _ _ _ [34,68,130,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34584

theorem m42158_40 : Upper (D 7) (R 7) [34,68,130,257,40] 13 :=
  permutation_upper _ _ _ [34,68,130,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34593

theorem m42158_65 : Upper (D 7) (R 7) [34,68,130,257,65] 13 :=
  permutation_upper _ _ _ [34,68,130,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34600

theorem m42158_72 : Upper (D 7) (R 7) [34,68,130,257,72] 13 :=
  permutation_upper _ _ _ [34,68,130,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34607

theorem m42158_96 : Upper (D 7) (R 7) [34,68,130,257,96] 13 :=
  permutation_upper _ _ _ [34,68,130,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34613

theorem m42158_129 : Upper (D 7) (R 7) [34,68,130,257,129] 13 :=
  permutation_upper _ _ _ [34,68,130,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34616

theorem m42158_136 : Upper (D 7) (R 7) [34,68,130,257,136] 13 :=
  permutation_upper _ _ _ [34,68,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34620

theorem m42158_160 : Upper (D 7) (R 7) [34,68,130,257,160] 13 :=
  permutation_upper _ _ _ [34,68,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34624

theorem m42158_192 : Upper (D 7) (R 7) [34,68,130,257,192] 13 :=
  permutation_upper _ _ _ [34,68,130,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34627

def r42158 : Route 9 := (fun mask => (mask,id))

def c42158 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42158 : Upper (D 7) (R 7) [34,68,130,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,257] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r42158 c42158
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42158_9
  · exact m42158_33
  · exact m42158_40
  · exact m42158_65
  · exact m42158_72
  · exact m42158_96
  · exact m42158_129
  · exact m42158_136
  · exact m42158_160
  · exact m42158_192

theorem m42159_9 : Upper (D 7) (R 7) [34,68,130,272,9] 13 :=
  permutation_upper _ _ _ [34,68,130,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34576

theorem m42159_33 : Upper (D 7) (R 7) [34,68,130,272,33] 13 :=
  permutation_upper _ _ _ [34,68,130,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34585

theorem m42159_40 : Upper (D 7) (R 7) [34,68,130,272,40] 13 :=
  permutation_upper _ _ _ [34,68,130,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34594

theorem m42159_65 : Upper (D 7) (R 7) [34,68,130,272,65] 13 :=
  permutation_upper _ _ _ [34,68,130,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34601

theorem m42159_72 : Upper (D 7) (R 7) [34,68,130,272,72] 13 :=
  permutation_upper _ _ _ [34,68,130,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34608

theorem m42159_96 : Upper (D 7) (R 7) [34,68,130,272,96] 13 :=
  permutation_upper _ _ _ [34,68,130,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34614

theorem m42159_129 : Upper (D 7) (R 7) [34,68,130,272,129] 13 :=
  permutation_upper _ _ _ [34,68,130,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34617

theorem m42159_136 : Upper (D 7) (R 7) [34,68,130,272,136] 13 :=
  permutation_upper _ _ _ [34,68,130,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34621

theorem m42159_160 : Upper (D 7) (R 7) [34,68,130,272,160] 13 :=
  permutation_upper _ _ _ [34,68,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34625

theorem m42159_192 : Upper (D 7) (R 7) [34,68,130,272,192] 13 :=
  permutation_upper _ _ _ [34,68,130,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34628

def r42159 : Route 9 := (fun mask => (mask,id))

def c42159 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42159 : Upper (D 7) (R 7) [34,68,130,272] 13 := by
  apply FastRouting.sound _ _ [34,68,130,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r42159 c42159
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42159_9
  · exact m42159_33
  · exact m42159_40
  · exact m42159_65
  · exact m42159_72
  · exact m42159_96
  · exact m42159_129
  · exact m42159_136
  · exact m42159_160
  · exact m42159_192

theorem m42160_9 : Upper (D 7) (R 7) [34,68,130,288,9] 13 :=
  permutation_upper _ _ _ [34,68,130,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34577

theorem m42160_65 : Upper (D 7) (R 7) [34,68,130,288,65] 13 :=
  permutation_upper _ _ _ [34,68,130,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34602

theorem m42160_72 : Upper (D 7) (R 7) [34,68,130,288,72] 13 :=
  permutation_upper _ _ _ [34,68,130,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34609

theorem m42160_129 : Upper (D 7) (R 7) [34,68,130,288,129] 13 :=
  permutation_upper _ _ _ [34,68,130,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34618

theorem m42160_136 : Upper (D 7) (R 7) [34,68,130,288,136] 13 :=
  permutation_upper _ _ _ [34,68,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34622

theorem m42160_192 : Upper (D 7) (R 7) [34,68,130,288,192] 13 :=
  permutation_upper _ _ _ [34,68,130,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34629

def r42160 : Route 9 := (fun mask => (mask,id))

def c42160 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42160 : Upper (D 7) (R 7) [34,68,130,288] 13 := by
  apply FastRouting.sound _ _ [34,68,130,288] 13 (by decide) (choices 2) [9,65,72,129,136,192] r42160 c42160
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42160_9
  · exact m42160_65
  · exact m42160_72
  · exact m42160_129
  · exact m42160_136
  · exact m42160_192

theorem m42161_9 : Upper (D 7) (R 7) [34,68,130,320,9] 13 :=
  permutation_upper _ _ _ [34,68,130,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34578

theorem m42161_33 : Upper (D 7) (R 7) [34,68,130,320,33] 13 :=
  permutation_upper _ _ _ [34,68,130,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34586

theorem m42161_40 : Upper (D 7) (R 7) [34,68,130,320,40] 13 :=
  permutation_upper _ _ _ [34,68,130,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34595

theorem m42161_129 : Upper (D 7) (R 7) [34,68,130,320,129] 13 :=
  permutation_upper _ _ _ [34,68,130,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34619

theorem m42161_136 : Upper (D 7) (R 7) [34,68,130,320,136] 13 :=
  permutation_upper _ _ _ [34,68,130,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34623

theorem m42161_160 : Upper (D 7) (R 7) [34,68,130,320,160] 13 :=
  permutation_upper _ _ _ [34,68,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34626

def r42161 : Route 9 := (fun mask => (mask,id))

def c42161 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42161 : Upper (D 7) (R 7) [34,68,130,320] 13 := by
  apply FastRouting.sound _ _ [34,68,130,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r42161 c42161
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42161_9
  · exact m42161_33
  · exact m42161_40
  · exact m42161_129
  · exact m42161_136
  · exact m42161_160

theorem m42162_9 : Upper (D 7) (R 7) [34,68,130,384,9] 13 :=
  permutation_upper _ _ _ [34,68,130,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34579

theorem m42162_33 : Upper (D 7) (R 7) [34,68,130,384,33] 13 :=
  permutation_upper _ _ _ [34,68,130,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34587

theorem m42162_40 : Upper (D 7) (R 7) [34,68,130,384,40] 13 :=
  permutation_upper _ _ _ [34,68,130,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34596

theorem m42162_65 : Upper (D 7) (R 7) [34,68,130,384,65] 13 :=
  permutation_upper _ _ _ [34,68,130,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34603

theorem m42162_72 : Upper (D 7) (R 7) [34,68,130,384,72] 13 :=
  permutation_upper _ _ _ [34,68,130,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34610

theorem m42162_96 : Upper (D 7) (R 7) [34,68,130,384,96] 13 :=
  permutation_upper _ _ _ [34,68,130,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u34615

def r42162 : Route 9 := (fun mask => (mask,id))

def c42162 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42162 : Upper (D 7) (R 7) [34,68,130,384] 13 := by
  apply FastRouting.sound _ _ [34,68,130,384] 13 (by decide) (choices 2) [9,33,40,65,72,96] r42162 c42162
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42162_9
  · exact m42162_33
  · exact m42162_40
  · exact m42162_65
  · exact m42162_72
  · exact m42162_96

def b42163 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 140 11 497 497 497 497 497), lower := (rows 35 70 140 11 16 32 64 128 256), losses := [] }

theorem u42163 : Upper (D 7) (R 7) [34,68,136,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42164 : Route 9 := (fun mask => (mask,id))

def c42164 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42164 : Upper (D 7) (R 7) [34,68,136,17] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r42164 c42164
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34630
  · exact u34631
  · exact u34632
  · exact u34633
  · exact u34634
  · exact u34635
  · exact u34636
  · exact u34637
  · exact u34638
  · exact u34639
  · exact u34640
  · exact u34641
  · exact u34642
  · exact u34643
  · exact u34644

def r42165 : Route 9 := (fun mask => (mask,id))

def c42165 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u42165 : Upper (D 7) (R 7) [34,68,136,18] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r42165 c42165
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34645
  · exact u34646
  · exact u34647
  · exact u34648
  · exact u34649
  · exact u34650
  · exact u34651
  · exact u34652
  · exact u34653
  · exact u34654

def b42166 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 140 41 467 499 467 467 467), lower := (rows 35 70 140 41 16 32 64 128 256), losses := [] }

theorem u42166 : Upper (D 7) (R 7) [34,68,136,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42167 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 140 42 465 497 465 465 465), lower := (rows 35 70 140 42 16 32 64 128 256), losses := [] }

theorem u42167 : Upper (D 7) (R 7) [34,68,136,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42168 : Route 9 := (fun mask => (mask,id))

def c42168 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42168 : Upper (D 7) (R 7) [34,68,136,48] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r42168 c42168
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34655
  · exact u34656
  · exact u34657
  · exact u34658
  · exact u34659
  · exact u34660
  · exact u34661
  · exact u34662
  · exact u34663
  · exact u34664

def r42169 : Route 9 := (fun mask => (mask,id))

def c42169 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42169 : Upper (D 7) (R 7) [34,68,136,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r42169 c42169
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34665
  · exact u34666
  · exact u34667
  · exact u34668
  · exact u34669
  · exact u34670
  · exact u34671
  · exact u34672
  · exact u34673
  · exact u34674

def b42170 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 35 70 140 74 433 433 497 433 433), lower := (rows 35 70 140 74 16 32 64 128 256), losses := [] }

theorem u42170 : Upper (D 7) (R 7) [34,68,136,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42171 : Route 9 := (fun mask => (mask,id))

def c42171 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42171 : Upper (D 7) (R 7) [34,68,136,80] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r42171 c42171
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34675
  · exact u34676
  · exact u34677
  · exact u34678
  · exact u34679
  · exact u34680
  · exact u34681
  · exact u34682
  · exact u34683
  · exact u34684

def r42172 : Route 9 := (fun mask => (mask,id))

def c42172 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42172 : Upper (D 7) (R 7) [34,68,136,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42172 c42172
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34685
  · exact u34686
  · exact u34687
  · exact u34688
  · exact u34689
  · exact u34690

def b42173 : PairBound 9 := { available := 371, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 70 140 137 371 371 371 499 371), lower := (rows 35 70 140 137 16 32 64 128 256), losses := [] }

theorem u42173 : Upper (D 7) (R 7) [34,68,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42174 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 70 140 138 369 369 369 497 369), lower := (rows 35 70 140 138 16 32 64 128 256), losses := [] }

theorem u42174 : Upper (D 7) (R 7) [34,68,136,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42175 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 70 140 152 371 355 355 483 355), lower := (rows 35 70 140 152 16 32 64 128 256), losses := [] }

theorem u42175 : Upper (D 7) (R 7) [34,68,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42176 : PairBound 9 := { available := 339, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 35 70 140 168 339 371 339 467 339), lower := (rows 35 70 140 168 16 32 64 128 256), losses := [] }

theorem u42176 : Upper (D 7) (R 7) [34,68,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42177 : PairBound 9 := { available := 307, camps := [{ cop := 3, region := 6, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 140 200 307 307 371 435 307), lower := (rows 35 70 140 200 16 32 64 128 256), losses := [] }

theorem u42177 : Upper (D 7) (R 7) [34,68,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42178 : Route 9 := (fun mask => (mask,id))

def c42178 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42178 : Upper (D 7) (R 7) [34,68,136,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r42178 c42178
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34691
  · exact u34692
  · exact u34693
  · exact u34694
  · exact u34695
  · exact u34696
  · exact u34697
  · exact u34698
  · exact u34699
  · exact u34700

def r42179 : Route 9 := (fun mask => (mask,id))

def c42179 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42179 : Upper (D 7) (R 7) [34,68,136,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r42179 c42179
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u34701
  · exact u34702
  · exact u34703
  · exact u34704
  · exact u34705
  · exact u34706

#print axioms u42179
end Delivery.IrregularNine14.P07
