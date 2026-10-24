import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0623
import IrregularNine14P07C0624
import IrregularNine14P07C0625
import IrregularNine14P07C0626
import IrregularNine14P07C0627

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m42960_3 : Upper (D 7) (R 7) [36,96,24,384,3] 13 :=
  permutation_upper _ _ _ [36,96,24,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37388

theorem m42960_65 : Upper (D 7) (R 7) [36,96,24,384,65] 13 :=
  permutation_upper _ _ _ [36,96,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37393

theorem m42960_66 : Upper (D 7) (R 7) [36,96,24,384,66] 13 :=
  permutation_upper _ _ _ [36,96,24,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37398

theorem m42960_129 : Upper (D 7) (R 7) [36,96,24,384,129] 13 :=
  permutation_upper _ _ _ [36,96,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37405

theorem m42960_130 : Upper (D 7) (R 7) [36,96,24,384,130] 13 :=
  permutation_upper _ _ _ [36,96,24,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37411

theorem m42960_192 : Upper (D 7) (R 7) [36,96,24,384,192] 13 :=
  permutation_upper _ _ _ [36,96,24,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37414

def r42960 : Route 9 := (fun mask => (mask,id))

def c42960 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42960 : Upper (D 7) (R 7) [36,96,24,384] 13 := by
  apply FastRouting.sound _ _ [36,96,24,384] 13 (by decide) (choices 2) [3,65,66,129,130,192] r42960 c42960
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42960_3
  · exact m42960_65
  · exact m42960_66
  · exact m42960_129
  · exact m42960_130
  · exact m42960_192

def b42961 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 13, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(0,7),(2,5),(2,7),(3,7)], upper := (rows 37 98 76 11 403 435 467 403 403), lower := (rows 37 98 76 11 16 32 64 128 256), losses := [] }

theorem u42961 : Upper (D 7) (R 7) [36,96,72,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42962 : Route 9 := (fun mask => (mask,id))

def c42962 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42962 : Upper (D 7) (R 7) [36,96,72,17] 13 := by
  apply FastRouting.sound _ _ [36,96,72,17] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42962 c42962
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37415
  · exact u37416
  · exact u37417
  · exact u37418
  · exact u37419
  · exact u37420

def r42963 : Route 9 := (fun mask => (mask,id))

def c42963 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42963 : Upper (D 7) (R 7) [36,96,72,18] 13 := by
  apply FastRouting.sound _ _ [36,96,72,18] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42963 c42963
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37421
  · exact u37422
  · exact u37423
  · exact u37424
  · exact u37425
  · exact u37426

def r42964 : Route 9 := (fun mask => (mask,id))

def c42964 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42964 : Upper (D 7) (R 7) [36,96,72,129] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42964 c42964
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37427
  · exact u37428
  · exact u37429
  · exact u37430
  · exact u37431
  · exact u37432

def r42965 : Route 9 := (fun mask => (mask,id))

def c42965 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42965 : Upper (D 7) (R 7) [36,96,72,130] 13 := by
  apply FastRouting.sound _ _ [36,96,72,130] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42965 c42965
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37433
  · exact u37434
  · exact u37435
  · exact u37436
  · exact u37437
  · exact u37438

def r42966 : Route 9 := (fun mask => (mask,id))

def c42966 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42966 : Upper (D 7) (R 7) [36,96,72,144] 13 := by
  apply FastRouting.sound _ _ [36,96,72,144] 13 (by decide) (choices 2) [3,129,130,257,258,384] r42966 c42966
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37439
  · exact u37440
  · exact u37441
  · exact u37442
  · exact u37443
  · exact u37444

def r42967 : Route 9 := (fun mask => (mask,id))

def c42967 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42967 : Upper (D 7) (R 7) [36,96,72,257] 13 := by
  apply FastRouting.sound _ _ [36,96,72,257] 13 (by decide) (choices 2) [3,129,130] r42967 c42967
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37445
  · exact u37446
  · exact u37447

def r42968 : Route 9 := (fun mask => (mask,id))

def c42968 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42968 : Upper (D 7) (R 7) [36,96,72,258] 13 := by
  apply FastRouting.sound _ _ [36,96,72,258] 13 (by decide) (choices 2) [3,129,130] r42968 c42968
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37448
  · exact u37449
  · exact u37450

def r42969 : Route 9 := (fun mask => (mask,id))

def c42969 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42969 : Upper (D 7) (R 7) [36,96,72,272] 13 := by
  apply FastRouting.sound _ _ [36,96,72,272] 13 (by decide) (choices 2) [3,129,130] r42969 c42969
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37451
  · exact u37452
  · exact u37453

def r42970 : Route 9 := (fun mask => (mask,id))

def c42970 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42970 : Upper (D 7) (R 7) [36,96,72,384] 13 := by
  apply FastRouting.sound _ _ [36,96,72,384] 13 (by decide) (choices 2) [3,129,130] r42970 c42970
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37454
  · exact u37455
  · exact u37456

def b42971 : PairBound 9 := { available := 474, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 133 11 474 506 474 474 474), lower := (rows 37 98 133 11 16 32 64 128 256), losses := [] }

theorem u42971 : Upper (D 7) (R 7) [36,96,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r42972 : Route 9 := (fun mask => (mask,id))

def c42972 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42972 : Upper (D 7) (R 7) [36,96,129,17] 13 := by
  apply FastRouting.sound _ _ [36,96,129,17] 13 (by decide) (choices 2) [10,66,72,130,136,192,258,264,320,384] r42972 c42972
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37466
  · exact u37467
  · exact u37468
  · exact u37469
  · exact u37470
  · exact u37471
  · exact u37472
  · exact u37473
  · exact u37474
  · exact u37475

theorem m42973_3 : Upper (D 7) (R 7) [36,96,129,18,3] 13 :=
  permutation_upper _ _ _ [36,96,129,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37457

theorem m42973_9 : Upper (D 7) (R 7) [36,96,129,18,9] 13 :=
  permutation_upper _ _ _ [36,96,129,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37466

def r42973 : Route 9 := (fun mask => (mask,id))

def c42973 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42973 : Upper (D 7) (R 7) [36,96,129,18] 13 := by
  apply FastRouting.sound _ _ [36,96,129,18] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,257,258,264,320,384] r42973 c42973
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42973_3
  · exact m42973_9
  · exact u37476
  · exact u37477
  · exact u37478
  · exact u37479
  · exact u37480
  · exact u37481
  · exact u37482
  · exact u37483
  · exact u37484
  · exact u37485
  · exact u37486
  · exact u37487
  · exact u37488

theorem m42974_10 : Upper (D 7) (R 7) [36,96,129,65,10] 13 :=
  permutation_upper _ _ _ [36,96,129,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37477

def r42974 : Route 9 := (fun mask => (mask,id))

def c42974 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42974 : Upper (D 7) (R 7) [36,96,129,65] 13 := by
  apply FastRouting.sound _ _ [36,96,129,65] 13 (by decide) (choices 2) [10,130,136,258,264,384] r42974 c42974
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42974_10
  · exact u37489
  · exact u37490
  · exact u37491
  · exact u37492
  · exact u37493

def b42975 : PairBound 9 := { available := 411, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 133 74 411 443 475 411 411), lower := (rows 37 98 133 74 16 32 64 128 256), losses := [] }

theorem u42975 : Upper (D 7) (R 7) [36,96,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42976_3 : Upper (D 7) (R 7) [36,96,129,80,3] 13 :=
  permutation_upper _ _ _ [36,96,129,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37458

theorem m42976_9 : Upper (D 7) (R 7) [36,96,129,80,9] 13 :=
  permutation_upper _ _ _ [36,96,129,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37468

theorem m42976_10 : Upper (D 7) (R 7) [36,96,129,80,10] 13 :=
  permutation_upper _ _ _ [36,96,129,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37479

def r42976 : Route 9 := (fun mask => (mask,id))

def c42976 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42976 : Upper (D 7) (R 7) [36,96,129,80] 13 := by
  apply FastRouting.sound _ _ [36,96,129,80] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r42976 c42976
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42976_3
  · exact m42976_9
  · exact m42976_10
  · exact u37500
  · exact u37501
  · exact u37502
  · exact u37503
  · exact u37504
  · exact u37505
  · exact u37506

def b42977 : PairBound 9 := { available := 346, camps := [{ cop := 2, region := 8, targets := 98 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,5),(3,6)], upper := (rows 37 98 133 137 346 378 346 474 346), lower := (rows 37 98 133 137 16 32 64 128 256), losses := [] }

theorem u42977 : Upper (D 7) (R 7) [36,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42977 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42978_3 : Upper (D 7) (R 7) [36,96,129,130,3] 13 :=
  permutation_upper _ _ _ [36,96,129,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37459

theorem m42978_9 : Upper (D 7) (R 7) [36,96,129,130,9] 13 :=
  permutation_upper _ _ _ [36,96,129,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37469

theorem m42978_10 : Upper (D 7) (R 7) [36,96,129,130,10] 13 :=
  permutation_upper _ _ _ [36,96,129,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37481

theorem m42978_65 : Upper (D 7) (R 7) [36,96,129,130,65] 13 :=
  permutation_upper _ _ _ [36,96,129,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37489

theorem m42978_66 : Upper (D 7) (R 7) [36,96,129,130,66] 13 :=
  permutation_upper _ _ _ [36,96,129,66,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37494

theorem m42978_72 : Upper (D 7) (R 7) [36,96,129,130,72] 13 :=
  permutation_upper _ _ _ [36,96,129,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37501

def r42978 : Route 9 := (fun mask => (mask,id))

def c42978 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42978 : Upper (D 7) (R 7) [36,96,129,130] 13 := by
  apply FastRouting.sound _ _ [36,96,129,130] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r42978 c42978
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42978_3
  · exact m42978_9
  · exact m42978_10
  · exact m42978_65
  · exact m42978_66
  · exact m42978_72
  · exact u37510
  · exact u37511
  · exact u37512
  · exact u37513

theorem m42979_3 : Upper (D 7) (R 7) [36,96,129,144,3] 13 :=
  permutation_upper _ _ _ [36,96,129,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37460

theorem m42979_9 : Upper (D 7) (R 7) [36,96,129,144,9] 13 :=
  permutation_upper _ _ _ [36,96,129,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37470

theorem m42979_10 : Upper (D 7) (R 7) [36,96,129,144,10] 13 :=
  permutation_upper _ _ _ [36,96,129,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37482

theorem m42979_65 : Upper (D 7) (R 7) [36,96,129,144,65] 13 :=
  permutation_upper _ _ _ [36,96,129,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37490

theorem m42979_66 : Upper (D 7) (R 7) [36,96,129,144,66] 13 :=
  permutation_upper _ _ _ [36,96,129,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37495

theorem m42979_72 : Upper (D 7) (R 7) [36,96,129,144,72] 13 :=
  permutation_upper _ _ _ [36,96,129,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37502

def r42979 : Route 9 := (fun mask => (mask,id))

def c42979 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42979 : Upper (D 7) (R 7) [36,96,129,144] 13 := by
  apply FastRouting.sound _ _ [36,96,129,144] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r42979 c42979
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42979_3
  · exact m42979_9
  · exact m42979_10
  · exact m42979_65
  · exact m42979_66
  · exact m42979_72
  · exact u37514
  · exact u37515
  · exact u37516
  · exact u37517

theorem m42980_3 : Upper (D 7) (R 7) [36,96,129,192,3] 13 :=
  permutation_upper _ _ _ [36,96,129,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37461

theorem m42980_9 : Upper (D 7) (R 7) [36,96,129,192,9] 13 :=
  permutation_upper _ _ _ [36,96,129,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37471

theorem m42980_10 : Upper (D 7) (R 7) [36,96,129,192,10] 13 :=
  permutation_upper _ _ _ [36,96,129,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37483

def r42980 : Route 9 := (fun mask => (mask,id))

def c42980 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42980 : Upper (D 7) (R 7) [36,96,129,192] 13 := by
  apply FastRouting.sound _ _ [36,96,129,192] 13 (by decide) (choices 2) [3,9,10,257,258,264] r42980 c42980
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42980_3
  · exact m42980_9
  · exact m42980_10
  · exact u37518
  · exact u37519
  · exact u37520

theorem m42981_10 : Upper (D 7) (R 7) [36,96,129,257,10] 13 :=
  permutation_upper _ _ _ [36,96,129,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37484

theorem m42981_66 : Upper (D 7) (R 7) [36,96,129,257,66] 13 :=
  permutation_upper _ _ _ [36,96,129,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37496

theorem m42981_72 : Upper (D 7) (R 7) [36,96,129,257,72] 13 :=
  permutation_upper _ _ _ [36,96,129,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37503

theorem m42981_130 : Upper (D 7) (R 7) [36,96,129,257,130] 13 :=
  permutation_upper _ _ _ [36,96,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37510

theorem m42981_136 : Upper (D 7) (R 7) [36,96,129,257,136] 13 :=
  permutation_upper _ _ _ [36,96,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37514

theorem m42981_192 : Upper (D 7) (R 7) [36,96,129,257,192] 13 :=
  permutation_upper _ _ _ [36,96,129,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37518

def r42981 : Route 9 := (fun mask => (mask,id))

def c42981 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42981 : Upper (D 7) (R 7) [36,96,129,257] 13 := by
  apply FastRouting.sound _ _ [36,96,129,257] 13 (by decide) (choices 2) [10,66,72,130,136,192] r42981 c42981
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42981_10
  · exact m42981_66
  · exact m42981_72
  · exact m42981_130
  · exact m42981_136
  · exact m42981_192

theorem m42982_3 : Upper (D 7) (R 7) [36,96,129,258,3] 13 :=
  permutation_upper _ _ _ [36,96,129,3,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37462

theorem m42982_9 : Upper (D 7) (R 7) [36,96,129,258,9] 13 :=
  permutation_upper _ _ _ [36,96,129,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37472

theorem m42982_10 : Upper (D 7) (R 7) [36,96,129,258,10] 13 :=
  permutation_upper _ _ _ [36,96,129,18,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37485

theorem m42982_65 : Upper (D 7) (R 7) [36,96,129,258,65] 13 :=
  permutation_upper _ _ _ [36,96,129,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37491

theorem m42982_66 : Upper (D 7) (R 7) [36,96,129,258,66] 13 :=
  permutation_upper _ _ _ [36,96,129,66,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37497

theorem m42982_72 : Upper (D 7) (R 7) [36,96,129,258,72] 13 :=
  permutation_upper _ _ _ [36,96,129,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37504

theorem m42982_129 : Upper (D 7) (R 7) [36,96,129,258,129] 13 :=
  permutation_upper _ _ _ [36,96,129,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37507

theorem m42982_130 : Upper (D 7) (R 7) [36,96,129,258,130] 13 :=
  permutation_upper _ _ _ [36,96,129,130,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37511

theorem m42982_136 : Upper (D 7) (R 7) [36,96,129,258,136] 13 :=
  permutation_upper _ _ _ [36,96,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37515

theorem m42982_192 : Upper (D 7) (R 7) [36,96,129,258,192] 13 :=
  permutation_upper _ _ _ [36,96,129,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37519

def r42982 : Route 9 := (fun mask => (mask,id))

def c42982 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42982 : Upper (D 7) (R 7) [36,96,129,258] 13 := by
  apply FastRouting.sound _ _ [36,96,129,258] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42982 c42982
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42982_3
  · exact m42982_9
  · exact m42982_10
  · exact m42982_65
  · exact m42982_66
  · exact m42982_72
  · exact m42982_129
  · exact m42982_130
  · exact m42982_136
  · exact m42982_192

theorem m42983_3 : Upper (D 7) (R 7) [36,96,129,272,3] 13 :=
  permutation_upper _ _ _ [36,96,129,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37463

theorem m42983_9 : Upper (D 7) (R 7) [36,96,129,272,9] 13 :=
  permutation_upper _ _ _ [36,96,129,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37473

theorem m42983_10 : Upper (D 7) (R 7) [36,96,129,272,10] 13 :=
  permutation_upper _ _ _ [36,96,129,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37486

theorem m42983_65 : Upper (D 7) (R 7) [36,96,129,272,65] 13 :=
  permutation_upper _ _ _ [36,96,129,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37492

theorem m42983_66 : Upper (D 7) (R 7) [36,96,129,272,66] 13 :=
  permutation_upper _ _ _ [36,96,129,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37498

theorem m42983_72 : Upper (D 7) (R 7) [36,96,129,272,72] 13 :=
  permutation_upper _ _ _ [36,96,129,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37505

theorem m42983_129 : Upper (D 7) (R 7) [36,96,129,272,129] 13 :=
  permutation_upper _ _ _ [36,96,129,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37508

theorem m42983_130 : Upper (D 7) (R 7) [36,96,129,272,130] 13 :=
  permutation_upper _ _ _ [36,96,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37512

theorem m42983_136 : Upper (D 7) (R 7) [36,96,129,272,136] 13 :=
  permutation_upper _ _ _ [36,96,129,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37516

theorem m42983_192 : Upper (D 7) (R 7) [36,96,129,272,192] 13 :=
  permutation_upper _ _ _ [36,96,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37520

def r42983 : Route 9 := (fun mask => (mask,id))

def c42983 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42983 : Upper (D 7) (R 7) [36,96,129,272] 13 := by
  apply FastRouting.sound _ _ [36,96,129,272] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42983 c42983
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42983_3
  · exact m42983_9
  · exact m42983_10
  · exact m42983_65
  · exact m42983_66
  · exact m42983_72
  · exact m42983_129
  · exact m42983_130
  · exact m42983_136
  · exact m42983_192

theorem m42984_3 : Upper (D 7) (R 7) [36,96,129,320,3] 13 :=
  permutation_upper _ _ _ [36,96,129,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37464

theorem m42984_9 : Upper (D 7) (R 7) [36,96,129,320,9] 13 :=
  permutation_upper _ _ _ [36,96,129,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37474

theorem m42984_10 : Upper (D 7) (R 7) [36,96,129,320,10] 13 :=
  permutation_upper _ _ _ [36,96,129,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37487

theorem m42984_129 : Upper (D 7) (R 7) [36,96,129,320,129] 13 :=
  permutation_upper _ _ _ [36,96,129,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37509

theorem m42984_130 : Upper (D 7) (R 7) [36,96,129,320,130] 13 :=
  permutation_upper _ _ _ [36,96,129,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37513

theorem m42984_136 : Upper (D 7) (R 7) [36,96,129,320,136] 13 :=
  permutation_upper _ _ _ [36,96,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37517

def r42984 : Route 9 := (fun mask => (mask,id))

def c42984 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42984 : Upper (D 7) (R 7) [36,96,129,320] 13 := by
  apply FastRouting.sound _ _ [36,96,129,320] 13 (by decide) (choices 2) [3,9,10,129,130,136] r42984 c42984
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42984_3
  · exact m42984_9
  · exact m42984_10
  · exact m42984_129
  · exact m42984_130
  · exact m42984_136

theorem m42985_3 : Upper (D 7) (R 7) [36,96,129,384,3] 13 :=
  permutation_upper _ _ _ [36,96,129,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37465

theorem m42985_9 : Upper (D 7) (R 7) [36,96,129,384,9] 13 :=
  permutation_upper _ _ _ [36,96,129,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37475

theorem m42985_10 : Upper (D 7) (R 7) [36,96,129,384,10] 13 :=
  permutation_upper _ _ _ [36,96,129,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37488

theorem m42985_65 : Upper (D 7) (R 7) [36,96,129,384,65] 13 :=
  permutation_upper _ _ _ [36,96,129,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37493

theorem m42985_66 : Upper (D 7) (R 7) [36,96,129,384,66] 13 :=
  permutation_upper _ _ _ [36,96,129,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37499

theorem m42985_72 : Upper (D 7) (R 7) [36,96,129,384,72] 13 :=
  permutation_upper _ _ _ [36,96,129,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37506

def r42985 : Route 9 := (fun mask => (mask,id))

def c42985 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42985 : Upper (D 7) (R 7) [36,96,129,384] 13 := by
  apply FastRouting.sound _ _ [36,96,129,384] 13 (by decide) (choices 2) [3,9,10,65,66,72] r42985 c42985
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42985_3
  · exact m42985_9
  · exact m42985_10
  · exact m42985_65
  · exact m42985_66
  · exact m42985_72

def r42986 : Route 9 := (fun mask => (mask,id))

def c42986 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42986 : Upper (D 7) (R 7) [36,96,130,3] 13 := by
  apply FastRouting.sound _ _ [36,96,130,3] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r42986 c42986
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37521
  · exact u37522
  · exact u37523
  · exact u37524
  · exact u37525
  · exact u37526
  · exact u37527
  · exact u37528
  · exact u37529
  · exact u37530

theorem m42987_3 : Upper (D 7) (R 7) [36,96,130,17,3] 13 :=
  permutation_upper _ _ _ [36,96,130,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37521

def r42987 : Route 9 := (fun mask => (mask,id))

def c42987 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42987 : Upper (D 7) (R 7) [36,96,130,17] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,257,258,264,320,384] r42987 c42987
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42987_3
  · exact u37531
  · exact u37532
  · exact u37533
  · exact u37534
  · exact u37535
  · exact u37536
  · exact u37537
  · exact u37538
  · exact u37539
  · exact u37540
  · exact u37541
  · exact u37542
  · exact u37543
  · exact u37544

theorem m42988_9 : Upper (D 7) (R 7) [36,96,130,18,9] 13 :=
  permutation_upper _ _ _ [36,96,130,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37532

def r42988 : Route 9 := (fun mask => (mask,id))

def c42988 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42988 : Upper (D 7) (R 7) [36,96,130,18] 13 := by
  apply FastRouting.sound _ _ [36,96,130,18] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r42988 c42988
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42988_9
  · exact u37545
  · exact u37546
  · exact u37547
  · exact u37548
  · exact u37549
  · exact u37550
  · exact u37551
  · exact u37552
  · exact u37553

theorem m42989_3 : Upper (D 7) (R 7) [36,96,130,65,3] 13 :=
  permutation_upper _ _ _ [36,96,130,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37522

theorem m42989_9 : Upper (D 7) (R 7) [36,96,130,65,9] 13 :=
  permutation_upper _ _ _ [36,96,130,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37533

theorem m42989_10 : Upper (D 7) (R 7) [36,96,130,65,10] 13 :=
  permutation_upper _ _ _ [36,96,130,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37545

def r42989 : Route 9 := (fun mask => (mask,id))

def c42989 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42989 : Upper (D 7) (R 7) [36,96,130,65] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r42989 c42989
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42989_3
  · exact m42989_9
  · exact m42989_10
  · exact u37554
  · exact u37555
  · exact u37556
  · exact u37557
  · exact u37558
  · exact u37559
  · exact u37560

def b42990 : PairBound 9 := { available := 409, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 134 74 409 441 473 409 409), lower := (rows 37 98 134 74 16 32 64 128 256), losses := [] }

theorem u42990 : Upper (D 7) (R 7) [36,96,130,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42991_3 : Upper (D 7) (R 7) [36,96,130,80,3] 13 :=
  permutation_upper _ _ _ [36,96,130,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37523

theorem m42991_9 : Upper (D 7) (R 7) [36,96,130,80,9] 13 :=
  permutation_upper _ _ _ [36,96,130,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37535

theorem m42991_10 : Upper (D 7) (R 7) [36,96,130,80,10] 13 :=
  permutation_upper _ _ _ [36,96,130,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37546

def r42991 : Route 9 := (fun mask => (mask,id))

def c42991 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42991 : Upper (D 7) (R 7) [36,96,130,80] 13 := by
  apply FastRouting.sound _ _ [36,96,130,80] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r42991 c42991
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42991_3
  · exact m42991_9
  · exact m42991_10
  · exact u37566
  · exact u37567
  · exact u37568
  · exact u37569
  · exact u37570
  · exact u37571
  · exact u37572

theorem m42992_3 : Upper (D 7) (R 7) [36,96,130,129,3] 13 :=
  permutation_upper _ _ _ [36,96,130,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37524

theorem m42992_9 : Upper (D 7) (R 7) [36,96,130,129,9] 13 :=
  permutation_upper _ _ _ [36,96,130,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37536

theorem m42992_10 : Upper (D 7) (R 7) [36,96,130,129,10] 13 :=
  permutation_upper _ _ _ [36,96,130,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37547

theorem m42992_65 : Upper (D 7) (R 7) [36,96,130,129,65] 13 :=
  permutation_upper _ _ _ [36,96,130,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37554

theorem m42992_66 : Upper (D 7) (R 7) [36,96,130,129,66] 13 :=
  permutation_upper _ _ _ [36,96,130,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37561

theorem m42992_72 : Upper (D 7) (R 7) [36,96,130,129,72] 13 :=
  permutation_upper _ _ _ [36,96,130,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37566

def r42992 : Route 9 := (fun mask => (mask,id))

def c42992 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42992 : Upper (D 7) (R 7) [36,96,130,129] 13 := by
  apply FastRouting.sound _ _ [36,96,130,129] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r42992 c42992
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42992_3
  · exact m42992_9
  · exact m42992_10
  · exact m42992_65
  · exact m42992_66
  · exact m42992_72
  · exact u37573
  · exact u37574
  · exact u37575
  · exact u37576

def b42993 : PairBound 9 := { available := 345, camps := [{ cop := 2, region := 8, targets := 97 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5),(3,6)], upper := (rows 37 98 134 138 345 377 345 473 345), lower := (rows 37 98 134 138 16 32 64 128 256), losses := [] }

theorem u42993 : Upper (D 7) (R 7) [36,96,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m42994_3 : Upper (D 7) (R 7) [36,96,130,144,3] 13 :=
  permutation_upper _ _ _ [36,96,130,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37525

theorem m42994_9 : Upper (D 7) (R 7) [36,96,130,144,9] 13 :=
  permutation_upper _ _ _ [36,96,130,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37538

theorem m42994_10 : Upper (D 7) (R 7) [36,96,130,144,10] 13 :=
  permutation_upper _ _ _ [36,96,130,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37548

theorem m42994_65 : Upper (D 7) (R 7) [36,96,130,144,65] 13 :=
  permutation_upper _ _ _ [36,96,130,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37556

theorem m42994_66 : Upper (D 7) (R 7) [36,96,130,144,66] 13 :=
  permutation_upper _ _ _ [36,96,130,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37562

theorem m42994_72 : Upper (D 7) (R 7) [36,96,130,144,72] 13 :=
  permutation_upper _ _ _ [36,96,130,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37568

def r42994 : Route 9 := (fun mask => (mask,id))

def c42994 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42994 : Upper (D 7) (R 7) [36,96,130,144] 13 := by
  apply FastRouting.sound _ _ [36,96,130,144] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r42994 c42994
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42994_3
  · exact m42994_9
  · exact m42994_10
  · exact m42994_65
  · exact m42994_66
  · exact m42994_72
  · exact u37580
  · exact u37581
  · exact u37582
  · exact u37583

theorem m42995_3 : Upper (D 7) (R 7) [36,96,130,192,3] 13 :=
  permutation_upper _ _ _ [36,96,130,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37526

theorem m42995_9 : Upper (D 7) (R 7) [36,96,130,192,9] 13 :=
  permutation_upper _ _ _ [36,96,130,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37539

theorem m42995_10 : Upper (D 7) (R 7) [36,96,130,192,10] 13 :=
  permutation_upper _ _ _ [36,96,130,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37549

def r42995 : Route 9 := (fun mask => (mask,id))

def c42995 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42995 : Upper (D 7) (R 7) [36,96,130,192] 13 := by
  apply FastRouting.sound _ _ [36,96,130,192] 13 (by decide) (choices 2) [3,9,10,257,258,264] r42995 c42995
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42995_3
  · exact m42995_9
  · exact m42995_10
  · exact u37584
  · exact u37585
  · exact u37586

theorem m42996_3 : Upper (D 7) (R 7) [36,96,130,257,3] 13 :=
  permutation_upper _ _ _ [36,96,130,3,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37527

theorem m42996_9 : Upper (D 7) (R 7) [36,96,130,257,9] 13 :=
  permutation_upper _ _ _ [36,96,130,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37540

theorem m42996_10 : Upper (D 7) (R 7) [36,96,130,257,10] 13 :=
  permutation_upper _ _ _ [36,96,130,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37550

theorem m42996_65 : Upper (D 7) (R 7) [36,96,130,257,65] 13 :=
  permutation_upper _ _ _ [36,96,130,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37557

theorem m42996_66 : Upper (D 7) (R 7) [36,96,130,257,66] 13 :=
  permutation_upper _ _ _ [36,96,130,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37563

theorem m42996_72 : Upper (D 7) (R 7) [36,96,130,257,72] 13 :=
  permutation_upper _ _ _ [36,96,130,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37569

theorem m42996_129 : Upper (D 7) (R 7) [36,96,130,257,129] 13 :=
  permutation_upper _ _ _ [36,96,130,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37573

theorem m42996_130 : Upper (D 7) (R 7) [36,96,130,257,130] 13 :=
  permutation_upper _ _ _ [36,96,130,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37577

theorem m42996_136 : Upper (D 7) (R 7) [36,96,130,257,136] 13 :=
  permutation_upper _ _ _ [36,96,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37580

theorem m42996_192 : Upper (D 7) (R 7) [36,96,130,257,192] 13 :=
  permutation_upper _ _ _ [36,96,130,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37584

def r42996 : Route 9 := (fun mask => (mask,id))

def c42996 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42996 : Upper (D 7) (R 7) [36,96,130,257] 13 := by
  apply FastRouting.sound _ _ [36,96,130,257] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42996 c42996
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42996_3
  · exact m42996_9
  · exact m42996_10
  · exact m42996_65
  · exact m42996_66
  · exact m42996_72
  · exact m42996_129
  · exact m42996_130
  · exact m42996_136
  · exact m42996_192

theorem m42997_9 : Upper (D 7) (R 7) [36,96,130,258,9] 13 :=
  permutation_upper _ _ _ [36,96,130,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37541

theorem m42997_65 : Upper (D 7) (R 7) [36,96,130,258,65] 13 :=
  permutation_upper _ _ _ [36,96,130,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37558

theorem m42997_72 : Upper (D 7) (R 7) [36,96,130,258,72] 13 :=
  permutation_upper _ _ _ [36,96,130,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37570

theorem m42997_129 : Upper (D 7) (R 7) [36,96,130,258,129] 13 :=
  permutation_upper _ _ _ [36,96,130,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37574

theorem m42997_136 : Upper (D 7) (R 7) [36,96,130,258,136] 13 :=
  permutation_upper _ _ _ [36,96,130,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37581

theorem m42997_192 : Upper (D 7) (R 7) [36,96,130,258,192] 13 :=
  permutation_upper _ _ _ [36,96,130,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37585

def r42997 : Route 9 := (fun mask => (mask,id))

def c42997 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42997 : Upper (D 7) (R 7) [36,96,130,258] 13 := by
  apply FastRouting.sound _ _ [36,96,130,258] 13 (by decide) (choices 2) [9,65,72,129,136,192] r42997 c42997
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42997_9
  · exact m42997_65
  · exact m42997_72
  · exact m42997_129
  · exact m42997_136
  · exact m42997_192

theorem m42998_3 : Upper (D 7) (R 7) [36,96,130,272,3] 13 :=
  permutation_upper _ _ _ [36,96,130,3,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37528

theorem m42998_9 : Upper (D 7) (R 7) [36,96,130,272,9] 13 :=
  permutation_upper _ _ _ [36,96,130,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37542

theorem m42998_10 : Upper (D 7) (R 7) [36,96,130,272,10] 13 :=
  permutation_upper _ _ _ [36,96,130,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37551

theorem m42998_65 : Upper (D 7) (R 7) [36,96,130,272,65] 13 :=
  permutation_upper _ _ _ [36,96,130,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37559

theorem m42998_66 : Upper (D 7) (R 7) [36,96,130,272,66] 13 :=
  permutation_upper _ _ _ [36,96,130,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37564

theorem m42998_72 : Upper (D 7) (R 7) [36,96,130,272,72] 13 :=
  permutation_upper _ _ _ [36,96,130,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37571

theorem m42998_129 : Upper (D 7) (R 7) [36,96,130,272,129] 13 :=
  permutation_upper _ _ _ [36,96,130,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37575

theorem m42998_130 : Upper (D 7) (R 7) [36,96,130,272,130] 13 :=
  permutation_upper _ _ _ [36,96,130,130,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37578

theorem m42998_136 : Upper (D 7) (R 7) [36,96,130,272,136] 13 :=
  permutation_upper _ _ _ [36,96,130,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37582

theorem m42998_192 : Upper (D 7) (R 7) [36,96,130,272,192] 13 :=
  permutation_upper _ _ _ [36,96,130,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37586

def r42998 : Route 9 := (fun mask => (mask,id))

def c42998 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u42998 : Upper (D 7) (R 7) [36,96,130,272] 13 := by
  apply FastRouting.sound _ _ [36,96,130,272] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r42998 c42998
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42998_3
  · exact m42998_9
  · exact m42998_10
  · exact m42998_65
  · exact m42998_66
  · exact m42998_72
  · exact m42998_129
  · exact m42998_130
  · exact m42998_136
  · exact m42998_192

theorem m42999_3 : Upper (D 7) (R 7) [36,96,130,320,3] 13 :=
  permutation_upper _ _ _ [36,96,130,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37529

theorem m42999_9 : Upper (D 7) (R 7) [36,96,130,320,9] 13 :=
  permutation_upper _ _ _ [36,96,130,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37543

theorem m42999_10 : Upper (D 7) (R 7) [36,96,130,320,10] 13 :=
  permutation_upper _ _ _ [36,96,130,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37552

theorem m42999_129 : Upper (D 7) (R 7) [36,96,130,320,129] 13 :=
  permutation_upper _ _ _ [36,96,130,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37576

theorem m42999_130 : Upper (D 7) (R 7) [36,96,130,320,130] 13 :=
  permutation_upper _ _ _ [36,96,130,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37579

theorem m42999_136 : Upper (D 7) (R 7) [36,96,130,320,136] 13 :=
  permutation_upper _ _ _ [36,96,130,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37583

def r42999 : Route 9 := (fun mask => (mask,id))

def c42999 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u42999 : Upper (D 7) (R 7) [36,96,130,320] 13 := by
  apply FastRouting.sound _ _ [36,96,130,320] 13 (by decide) (choices 2) [3,9,10,129,130,136] r42999 c42999
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42999_3
  · exact m42999_9
  · exact m42999_10
  · exact m42999_129
  · exact m42999_130
  · exact m42999_136

theorem m43000_3 : Upper (D 7) (R 7) [36,96,130,384,3] 13 :=
  permutation_upper _ _ _ [36,96,130,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37530

theorem m43000_9 : Upper (D 7) (R 7) [36,96,130,384,9] 13 :=
  permutation_upper _ _ _ [36,96,130,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37544

theorem m43000_10 : Upper (D 7) (R 7) [36,96,130,384,10] 13 :=
  permutation_upper _ _ _ [36,96,130,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37553

theorem m43000_65 : Upper (D 7) (R 7) [36,96,130,384,65] 13 :=
  permutation_upper _ _ _ [36,96,130,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37560

theorem m43000_66 : Upper (D 7) (R 7) [36,96,130,384,66] 13 :=
  permutation_upper _ _ _ [36,96,130,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37565

theorem m43000_72 : Upper (D 7) (R 7) [36,96,130,384,72] 13 :=
  permutation_upper _ _ _ [36,96,130,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37572

def r43000 : Route 9 := (fun mask => (mask,id))

def c43000 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43000 : Upper (D 7) (R 7) [36,96,130,384] 13 := by
  apply FastRouting.sound _ _ [36,96,130,384] 13 (by decide) (choices 2) [3,9,10,65,66,72] r43000 c43000
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43000_3
  · exact m43000_9
  · exact m43000_10
  · exact m43000_65
  · exact m43000_66
  · exact m43000_72

def r43001 : Route 9 := (fun mask => (mask,id))

def c43001 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43001 : Upper (D 7) (R 7) [36,96,136,3] 13 := by
  apply FastRouting.sound _ _ [36,96,136,3] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r43001 c43001
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37587
  · exact u37588
  · exact u37589
  · exact u37590
  · exact u37591
  · exact u37592
  · exact u37593
  · exact u37594
  · exact u37595
  · exact u37596

def r43002 : Route 9 := (fun mask => (mask,id))

def c43002 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43002 : Upper (D 7) (R 7) [36,96,136,17] 13 := by
  apply FastRouting.sound _ _ [36,96,136,17] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r43002 c43002
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37597
  · exact u37598
  · exact u37599
  · exact u37600
  · exact u37601
  · exact u37602
  · exact u37603
  · exact u37604
  · exact u37605
  · exact u37606

def r43003 : Route 9 := (fun mask => (mask,id))

def c43003 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u43003 : Upper (D 7) (R 7) [36,96,136,18] 13 := by
  apply FastRouting.sound _ _ [36,96,136,18] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r43003 c43003
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37607
  · exact u37608
  · exact u37609
  · exact u37610
  · exact u37611
  · exact u37612
  · exact u37613
  · exact u37614
  · exact u37615
  · exact u37616

def r43004 : Route 9 := (fun mask => (mask,id))

def c43004 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43004 : Upper (D 7) (R 7) [36,96,136,65] 13 := by
  apply FastRouting.sound _ _ [36,96,136,65] 13 (by decide) (choices 2) [3,129,130,257,258,384] r43004 c43004
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37617
  · exact u37618
  · exact u37619
  · exact u37620
  · exact u37621
  · exact u37622

def b43005 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 437, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 98 140 74 403 435 467 403 403), lower := (rows 37 98 140 74 16 32 64 128 256), losses := [] }

theorem u43005 : Upper (D 7) (R 7) [36,96,136,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43005 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43006 : Route 9 := (fun mask => (mask,id))

def c43006 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43006 : Upper (D 7) (R 7) [36,96,136,80] 13 := by
  apply FastRouting.sound _ _ [36,96,136,80] 13 (by decide) (choices 2) [3,129,130,257,258,384] r43006 c43006
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37623
  · exact u37624
  · exact u37625
  · exact u37626
  · exact u37627
  · exact u37628

def b43007 : PairBound 9 := { available := 339, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 98 140 137 339 371 339 467 339), lower := (rows 37 98 140 137 16 32 64 128 256), losses := [] }

theorem u43007 : Upper (D 7) (R 7) [36,96,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43008 : PairBound 9 := { available := 339, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 98 140 138 339 371 339 467 339), lower := (rows 37 98 140 138 16 32 64 128 256), losses := [] }

theorem u43008 : Upper (D 7) (R 7) [36,96,136,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43009 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 98 140 152 339 355 323 451 323), lower := (rows 37 98 140 152 16 32 64 128 256), losses := [] }

theorem u43009 : Upper (D 7) (R 7) [36,96,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43010 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 98 140 200 275 307 339 403 275), lower := (rows 37 98 140 200 16 32 64 128 256), losses := [] }

theorem u43010 : Upper (D 7) (R 7) [36,96,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43011 : Route 9 := (fun mask => (mask,id))

def c43011 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43011 : Upper (D 7) (R 7) [36,96,136,257] 13 := by
  apply FastRouting.sound _ _ [36,96,136,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43011 c43011
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37629
  · exact u37630
  · exact u37631
  · exact u37632
  · exact u37633
  · exact u37634

def r43012 : Route 9 := (fun mask => (mask,id))

def c43012 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43012 : Upper (D 7) (R 7) [36,96,136,258] 13 := by
  apply FastRouting.sound _ _ [36,96,136,258] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43012 c43012
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37635
  · exact u37636
  · exact u37637
  · exact u37638
  · exact u37639
  · exact u37640

def r43013 : Route 9 := (fun mask => (mask,id))

def c43013 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u43013 : Upper (D 7) (R 7) [36,96,136,272] 13 := by
  apply FastRouting.sound _ _ [36,96,136,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r43013 c43013
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37641
  · exact u37642
  · exact u37643
  · exact u37644
  · exact u37645
  · exact u37646

def r43014 : Route 9 := (fun mask => (mask,id))

def c43014 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u43014 : Upper (D 7) (R 7) [36,96,136,320] 13 := by
  apply FastRouting.sound _ _ [36,96,136,320] 13 (by decide) (choices 2) [3,129,130] r43014 c43014
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37647
  · exact u37648
  · exact u37649

def b43015 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 37 98 140 392 83 115 83 211 339), lower := (rows 37 98 140 392 16 32 64 128 256), losses := [] }

theorem u43015 : Upper (D 7) (R 7) [36,96,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r43016 : Route 9 := (fun mask => (mask,id))

def c43016 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43016 : Upper (D 7) (R 7) [36,96,192,3] 13 := by
  apply FastRouting.sound _ _ [36,96,192,3] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r43016 c43016
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37650
  · exact u37651
  · exact u37652
  · exact u37653
  · exact u37654
  · exact u37655
  · exact u37656
  · exact u37657
  · exact u37658
  · exact u37659

theorem m43017_3 : Upper (D 7) (R 7) [36,96,192,17,3] 13 :=
  permutation_upper _ _ _ [36,96,192,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37651

def r43017 : Route 9 := (fun mask => (mask,id))

def c43017 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43017 : Upper (D 7) (R 7) [36,96,192,17] 13 := by
  apply FastRouting.sound _ _ [36,96,192,17] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r43017 c43017
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43017_3
  · exact u37660
  · exact u37661
  · exact u37662
  · exact u37663
  · exact u37664
  · exact u37665
  · exact u37666
  · exact u37667
  · exact u37668

theorem m43018_3 : Upper (D 7) (R 7) [36,96,192,18,3] 13 :=
  permutation_upper _ _ _ [36,96,192,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37652

theorem m43018_9 : Upper (D 7) (R 7) [36,96,192,18,9] 13 :=
  permutation_upper _ _ _ [36,96,192,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37661

def r43018 : Route 9 := (fun mask => (mask,id))

def c43018 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u43018 : Upper (D 7) (R 7) [36,96,192,18] 13 := by
  apply FastRouting.sound _ _ [36,96,192,18] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r43018 c43018
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43018_3
  · exact m43018_9
  · exact u37669
  · exact u37670
  · exact u37671
  · exact u37672
  · exact u37673
  · exact u37674
  · exact u37675
  · exact u37676

theorem m43019_3 : Upper (D 7) (R 7) [36,96,192,129,3] 13 :=
  permutation_upper _ _ _ [36,96,192,3,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37653

theorem m43019_9 : Upper (D 7) (R 7) [36,96,192,129,9] 13 :=
  permutation_upper _ _ _ [36,96,192,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37662

theorem m43019_10 : Upper (D 7) (R 7) [36,96,192,129,10] 13 :=
  permutation_upper _ _ _ [36,96,192,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37670

def r43019 : Route 9 := (fun mask => (mask,id))

def c43019 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43019 : Upper (D 7) (R 7) [36,96,192,129] 13 := by
  apply FastRouting.sound _ _ [36,96,192,129] 13 (by decide) (choices 2) [3,9,10,257,258,264] r43019 c43019
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43019_3
  · exact m43019_9
  · exact m43019_10
  · exact u37677
  · exact u37678
  · exact u37679

#print axioms u43019
end Delivery.IrregularNine14.P07
