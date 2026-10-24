import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0623
import IrregularNine14P06C0624
import IrregularNine14P06C0625
import IrregularNine14P06C0626
import IrregularNine14P06C0627
import IrregularNine14P06C0628

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b42900 : PairBound 9 := { available := 92, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 292 11 92 124 92 220 348), lower := (rows 35 131 292 11 16 32 64 128 256), losses := [] }

theorem u42900 : Upper (D 6) (R 6) [34,129,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42901 : Route 9 := (fun mask => (mask,id))

def c42901 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42901 : Upper (D 6) (R 6) [34,129,288,5] 13 := by
  apply FastRouting.sound _ _ [34,129,288,5] 13 (by decide) (choices 2) [6,10,12,66,68,72] r42901 c42901
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37430
  · exact u37431
  · exact u37432
  · exact u37433
  · exact u37434
  · exact u37435

theorem m42902_5 : Upper (D 6) (R 6) [34,129,288,6,5] 13 :=
  permutation_upper _ _ _ [34,129,288,5,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37430

def r42902 : Route 9 := (fun mask => (mask,id))

def c42902 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42902 : Upper (D 6) (R 6) [34,129,288,6] 13 := by
  apply FastRouting.sound _ _ [34,129,288,6] 13 (by decide) (choices 2) [5,9,12,65,68,72] r42902 c42902
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42902_5
  · exact u37436
  · exact u37437
  · exact u37438
  · exact u37439
  · exact u37440

theorem m42903_6 : Upper (D 6) (R 6) [34,129,288,17,6] 13 :=
  permutation_upper _ _ _ [34,129,288,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37436

def r42903 : Route 9 := (fun mask => (mask,id))

def c42903 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42903 : Upper (D 6) (R 6) [34,129,288,17] 13 := by
  apply FastRouting.sound _ _ [34,129,288,17] 13 (by decide) (choices 2) [6,10,12,66,68,72] r42903 c42903
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42903_6
  · exact u37441
  · exact u37442
  · exact u37443
  · exact u37444
  · exact u37445

theorem m42904_5 : Upper (D 6) (R 6) [34,129,288,18,5] 13 :=
  permutation_upper _ _ _ [34,129,288,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37431

theorem m42904_9 : Upper (D 6) (R 6) [34,129,288,18,9] 13 :=
  permutation_upper _ _ _ [34,129,288,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37441

def r42904 : Route 9 := (fun mask => (mask,id))

def c42904 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42904 : Upper (D 6) (R 6) [34,129,288,18] 13 := by
  apply FastRouting.sound _ _ [34,129,288,18] 13 (by decide) (choices 2) [5,9,12,65,68,72] r42904 c42904
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42904_5
  · exact m42904_9
  · exact u37446
  · exact u37447
  · exact u37448
  · exact u37449

theorem m42905_3 : Upper (D 6) (R 6) [34,129,288,20,3] 13 :=
  permutation_upper _ _ _ [34,129,288,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37427

theorem m42905_5 : Upper (D 6) (R 6) [34,129,288,20,5] 13 :=
  permutation_upper _ _ _ [34,129,288,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37432

theorem m42905_6 : Upper (D 6) (R 6) [34,129,288,20,6] 13 :=
  permutation_upper _ _ _ [34,129,288,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37437

theorem m42905_9 : Upper (D 6) (R 6) [34,129,288,20,9] 13 :=
  permutation_upper _ _ _ [34,129,288,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37442

theorem m42905_10 : Upper (D 6) (R 6) [34,129,288,20,10] 13 :=
  permutation_upper _ _ _ [34,129,288,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37446

def r42905 : Route 9 := (fun mask => (mask,id))

def c42905 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42905 : Upper (D 6) (R 6) [34,129,288,20] 13 := by
  apply FastRouting.sound _ _ [34,129,288,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42905 c42905
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42905_3
  · exact m42905_5
  · exact m42905_6
  · exact m42905_9
  · exact m42905_10
  · exact u37450
  · exact u37451
  · exact u37452
  · exact u37453
  · exact u37454

theorem m42906_6 : Upper (D 6) (R 6) [34,129,288,65,6] 13 :=
  permutation_upper _ _ _ [34,129,288,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37438

theorem m42906_10 : Upper (D 6) (R 6) [34,129,288,65,10] 13 :=
  permutation_upper _ _ _ [34,129,288,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37447

theorem m42906_12 : Upper (D 6) (R 6) [34,129,288,65,12] 13 :=
  permutation_upper _ _ _ [34,129,288,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37451

def r42906 : Route 9 := (fun mask => (mask,id))

def c42906 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42906 : Upper (D 6) (R 6) [34,129,288,65] 13 := by
  apply FastRouting.sound _ _ [34,129,288,65] 13 (by decide) (choices 2) [6,10,12,66,68,72] r42906 c42906
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42906_6
  · exact m42906_10
  · exact m42906_12
  · exact u37455
  · exact u37456
  · exact u37457

theorem m42907_5 : Upper (D 6) (R 6) [34,129,288,66,5] 13 :=
  permutation_upper _ _ _ [34,129,288,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37433

theorem m42907_9 : Upper (D 6) (R 6) [34,129,288,66,9] 13 :=
  permutation_upper _ _ _ [34,129,288,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37443

theorem m42907_12 : Upper (D 6) (R 6) [34,129,288,66,12] 13 :=
  permutation_upper _ _ _ [34,129,288,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37452

theorem m42907_65 : Upper (D 6) (R 6) [34,129,288,66,65] 13 :=
  permutation_upper _ _ _ [34,129,288,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37455

def r42907 : Route 9 := (fun mask => (mask,id))

def c42907 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42907 : Upper (D 6) (R 6) [34,129,288,66] 13 := by
  apply FastRouting.sound _ _ [34,129,288,66] 13 (by decide) (choices 2) [5,9,12,65,68,72] r42907 c42907
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42907_5
  · exact m42907_9
  · exact m42907_12
  · exact m42907_65
  · exact u37458
  · exact u37459

theorem m42908_3 : Upper (D 6) (R 6) [34,129,288,68,3] 13 :=
  permutation_upper _ _ _ [34,129,288,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37428

theorem m42908_5 : Upper (D 6) (R 6) [34,129,288,68,5] 13 :=
  permutation_upper _ _ _ [34,129,288,5,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37434

theorem m42908_6 : Upper (D 6) (R 6) [34,129,288,68,6] 13 :=
  permutation_upper _ _ _ [34,129,288,6,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37439

theorem m42908_9 : Upper (D 6) (R 6) [34,129,288,68,9] 13 :=
  permutation_upper _ _ _ [34,129,288,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37444

theorem m42908_10 : Upper (D 6) (R 6) [34,129,288,68,10] 13 :=
  permutation_upper _ _ _ [34,129,288,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37448

theorem m42908_12 : Upper (D 6) (R 6) [34,129,288,68,12] 13 :=
  permutation_upper _ _ _ [34,129,288,20,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37453

theorem m42908_65 : Upper (D 6) (R 6) [34,129,288,68,65] 13 :=
  permutation_upper _ _ _ [34,129,288,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37456

theorem m42908_66 : Upper (D 6) (R 6) [34,129,288,68,66] 13 :=
  permutation_upper _ _ _ [34,129,288,66,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37458

def r42908 : Route 9 := (fun mask => (mask,id))

def c42908 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42908 : Upper (D 6) (R 6) [34,129,288,68] 13 := by
  apply FastRouting.sound _ _ [34,129,288,68] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42908 c42908
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42908_3
  · exact m42908_5
  · exact m42908_6
  · exact m42908_9
  · exact m42908_10
  · exact m42908_12
  · exact m42908_65
  · exact m42908_66
  · exact u37460
  · exact u37461

theorem m42909_3 : Upper (D 6) (R 6) [34,129,288,80,3] 13 :=
  permutation_upper _ _ _ [34,129,288,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37429

theorem m42909_5 : Upper (D 6) (R 6) [34,129,288,80,5] 13 :=
  permutation_upper _ _ _ [34,129,288,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37435

theorem m42909_6 : Upper (D 6) (R 6) [34,129,288,80,6] 13 :=
  permutation_upper _ _ _ [34,129,288,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37440

theorem m42909_9 : Upper (D 6) (R 6) [34,129,288,80,9] 13 :=
  permutation_upper _ _ _ [34,129,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37445

theorem m42909_10 : Upper (D 6) (R 6) [34,129,288,80,10] 13 :=
  permutation_upper _ _ _ [34,129,288,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37449

theorem m42909_12 : Upper (D 6) (R 6) [34,129,288,80,12] 13 :=
  permutation_upper _ _ _ [34,129,288,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37454

theorem m42909_65 : Upper (D 6) (R 6) [34,129,288,80,65] 13 :=
  permutation_upper _ _ _ [34,129,288,65,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37457

theorem m42909_66 : Upper (D 6) (R 6) [34,129,288,80,66] 13 :=
  permutation_upper _ _ _ [34,129,288,66,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37459

theorem m42909_68 : Upper (D 6) (R 6) [34,129,288,80,68] 13 :=
  permutation_upper _ _ _ [34,129,288,68,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37461

def r42909 : Route 9 := (fun mask => (mask,id))

def c42909 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42909 : Upper (D 6) (R 6) [34,129,288,80] 13 := by
  apply FastRouting.sound _ _ [34,129,288,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42909 c42909
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42909_3
  · exact m42909_5
  · exact m42909_6
  · exact m42909_9
  · exact m42909_10
  · exact m42909_12
  · exact m42909_65
  · exact m42909_66
  · exact m42909_68
  · exact u37462

def b42910 : PairBound 9 := { available := 124, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 324 11 124 124 124 252 380), lower := (rows 35 131 324 11 16 32 64 128 256), losses := [] }

theorem u42910 : Upper (D 6) (R 6) [34,129,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42911 : Route 9 := (fun mask => (mask,id))

def c42911 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42911 : Upper (D 6) (R 6) [34,129,320,5] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r42911 c42911
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37468
  · exact u37469
  · exact u37470
  · exact u37471
  · exact u37472
  · exact u37473
  · exact u37474
  · exact u37475
  · exact u37476
  · exact u37477

theorem m42912_5 : Upper (D 6) (R 6) [34,129,320,6,5] 13 :=
  permutation_upper _ _ _ [34,129,320,5,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37468

def r42912 : Route 9 := (fun mask => (mask,id))

def c42912 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42912 : Upper (D 6) (R 6) [34,129,320,6] 13 := by
  apply FastRouting.sound _ _ [34,129,320,6] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42912 c42912
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42912_5
  · exact u37478
  · exact u37479
  · exact u37480
  · exact u37481
  · exact u37482
  · exact u37483
  · exact u37484
  · exact u37485
  · exact u37486

theorem m42913_6 : Upper (D 6) (R 6) [34,129,320,17,6] 13 :=
  permutation_upper _ _ _ [34,129,320,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37478

def r42913 : Route 9 := (fun mask => (mask,id))

def c42913 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42913 : Upper (D 6) (R 6) [34,129,320,17] 13 := by
  apply FastRouting.sound _ _ [34,129,320,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r42913 c42913
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42913_6
  · exact u37487
  · exact u37488
  · exact u37489
  · exact u37490
  · exact u37491
  · exact u37492
  · exact u37493
  · exact u37494
  · exact u37495

theorem m42914_5 : Upper (D 6) (R 6) [34,129,320,18,5] 13 :=
  permutation_upper _ _ _ [34,129,320,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37469

theorem m42914_9 : Upper (D 6) (R 6) [34,129,320,18,9] 13 :=
  permutation_upper _ _ _ [34,129,320,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37487

def r42914 : Route 9 := (fun mask => (mask,id))

def c42914 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42914 : Upper (D 6) (R 6) [34,129,320,18] 13 := by
  apply FastRouting.sound _ _ [34,129,320,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r42914 c42914
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42914_5
  · exact m42914_9
  · exact u37496
  · exact u37497
  · exact u37498
  · exact u37499
  · exact u37500
  · exact u37501
  · exact u37502
  · exact u37503

theorem m42915_3 : Upper (D 6) (R 6) [34,129,320,20,3] 13 :=
  permutation_upper _ _ _ [34,129,320,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37463

theorem m42915_5 : Upper (D 6) (R 6) [34,129,320,20,5] 13 :=
  permutation_upper _ _ _ [34,129,320,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37470

theorem m42915_6 : Upper (D 6) (R 6) [34,129,320,20,6] 13 :=
  permutation_upper _ _ _ [34,129,320,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37479

theorem m42915_9 : Upper (D 6) (R 6) [34,129,320,20,9] 13 :=
  permutation_upper _ _ _ [34,129,320,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37488

theorem m42915_10 : Upper (D 6) (R 6) [34,129,320,20,10] 13 :=
  permutation_upper _ _ _ [34,129,320,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37496

def r42915 : Route 9 := (fun mask => (mask,id))

def c42915 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42915 : Upper (D 6) (R 6) [34,129,320,20] 13 := by
  apply FastRouting.sound _ _ [34,129,320,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r42915 c42915
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42915_3
  · exact m42915_5
  · exact m42915_6
  · exact m42915_9
  · exact m42915_10
  · exact u37504
  · exact u37505
  · exact u37506
  · exact u37507
  · exact u37508
  · exact u37509
  · exact u37510
  · exact u37511
  · exact u37512
  · exact u37513

def b42916 : PairBound 9 := { available := 94, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 324 41 94 126 94 222 350), lower := (rows 35 131 324 41 16 32 64 128 256), losses := [] }

theorem u42916 : Upper (D 6) (R 6) [34,129,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42917 : PairBound 9 := { available := 93, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 131 324 42 93 125 93 221 349), lower := (rows 35 131 324 42 16 32 64 128 256), losses := [] }

theorem u42917 : Upper (D 6) (R 6) [34,129,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42918_3 : Upper (D 6) (R 6) [34,129,320,36,3] 13 :=
  permutation_upper _ _ _ [34,129,320,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37464

theorem m42918_5 : Upper (D 6) (R 6) [34,129,320,36,5] 13 :=
  permutation_upper _ _ _ [34,129,320,5,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37472

theorem m42918_6 : Upper (D 6) (R 6) [34,129,320,36,6] 13 :=
  permutation_upper _ _ _ [34,129,320,6,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37481

theorem m42918_9 : Upper (D 6) (R 6) [34,129,320,36,9] 13 :=
  permutation_upper _ _ _ [34,129,320,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37490

theorem m42918_10 : Upper (D 6) (R 6) [34,129,320,36,10] 13 :=
  permutation_upper _ _ _ [34,129,320,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37498

theorem m42918_12 : Upper (D 6) (R 6) [34,129,320,36,12] 13 :=
  permutation_upper _ _ _ [34,129,320,20,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37507

def r42918 : Route 9 := (fun mask => (mask,id))

def c42918 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42918 : Upper (D 6) (R 6) [34,129,320,36] 13 := by
  apply FastRouting.sound _ _ [34,129,320,36] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42918 c42918
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42918_3
  · exact m42918_5
  · exact m42918_6
  · exact m42918_9
  · exact m42918_10
  · exact m42918_12
  · exact u37518
  · exact u37519
  · exact u37520
  · exact u37521

theorem m42919_3 : Upper (D 6) (R 6) [34,129,320,48,3] 13 :=
  permutation_upper _ _ _ [34,129,320,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37465

theorem m42919_5 : Upper (D 6) (R 6) [34,129,320,48,5] 13 :=
  permutation_upper _ _ _ [34,129,320,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37473

theorem m42919_6 : Upper (D 6) (R 6) [34,129,320,48,6] 13 :=
  permutation_upper _ _ _ [34,129,320,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37482

theorem m42919_9 : Upper (D 6) (R 6) [34,129,320,48,9] 13 :=
  permutation_upper _ _ _ [34,129,320,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37491

theorem m42919_10 : Upper (D 6) (R 6) [34,129,320,48,10] 13 :=
  permutation_upper _ _ _ [34,129,320,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37499

theorem m42919_12 : Upper (D 6) (R 6) [34,129,320,48,12] 13 :=
  permutation_upper _ _ _ [34,129,320,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37508

def r42919 : Route 9 := (fun mask => (mask,id))

def c42919 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42919 : Upper (D 6) (R 6) [34,129,320,48] 13 := by
  apply FastRouting.sound _ _ [34,129,320,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r42919 c42919
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42919_3
  · exact m42919_5
  · exact m42919_6
  · exact m42919_9
  · exact m42919_10
  · exact m42919_12
  · exact u37522
  · exact u37523
  · exact u37524
  · exact u37525

theorem m42920_6 : Upper (D 6) (R 6) [34,129,320,65,6] 13 :=
  permutation_upper _ _ _ [34,129,320,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37483

theorem m42920_10 : Upper (D 6) (R 6) [34,129,320,65,10] 13 :=
  permutation_upper _ _ _ [34,129,320,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37500

theorem m42920_12 : Upper (D 6) (R 6) [34,129,320,65,12] 13 :=
  permutation_upper _ _ _ [34,129,320,20,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37509

theorem m42920_34 : Upper (D 6) (R 6) [34,129,320,65,34] 13 :=
  permutation_upper _ _ _ [34,129,320,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37516

theorem m42920_36 : Upper (D 6) (R 6) [34,129,320,65,36] 13 :=
  permutation_upper _ _ _ [34,129,320,36,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37518

theorem m42920_40 : Upper (D 6) (R 6) [34,129,320,65,40] 13 :=
  permutation_upper _ _ _ [34,129,320,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37522

def r42920 : Route 9 := (fun mask => (mask,id))

def c42920 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42920 : Upper (D 6) (R 6) [34,129,320,65] 13 := by
  apply FastRouting.sound _ _ [34,129,320,65] 13 (by decide) (choices 2) [6,10,12,34,36,40] r42920 c42920
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42920_6
  · exact m42920_10
  · exact m42920_12
  · exact m42920_34
  · exact m42920_36
  · exact m42920_40

theorem m42921_5 : Upper (D 6) (R 6) [34,129,320,66,5] 13 :=
  permutation_upper _ _ _ [34,129,320,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37474

theorem m42921_9 : Upper (D 6) (R 6) [34,129,320,66,9] 13 :=
  permutation_upper _ _ _ [34,129,320,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37492

theorem m42921_12 : Upper (D 6) (R 6) [34,129,320,66,12] 13 :=
  permutation_upper _ _ _ [34,129,320,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37510

theorem m42921_33 : Upper (D 6) (R 6) [34,129,320,66,33] 13 :=
  permutation_upper _ _ _ [34,129,320,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37514

theorem m42921_36 : Upper (D 6) (R 6) [34,129,320,66,36] 13 :=
  permutation_upper _ _ _ [34,129,320,36,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37519

theorem m42921_40 : Upper (D 6) (R 6) [34,129,320,66,40] 13 :=
  permutation_upper _ _ _ [34,129,320,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37523

def r42921 : Route 9 := (fun mask => (mask,id))

def c42921 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42921 : Upper (D 6) (R 6) [34,129,320,66] 13 := by
  apply FastRouting.sound _ _ [34,129,320,66] 13 (by decide) (choices 2) [5,9,12,33,36,40] r42921 c42921
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42921_5
  · exact m42921_9
  · exact m42921_12
  · exact m42921_33
  · exact m42921_36
  · exact m42921_40

def b42922 : PairBound 9 := { available := 63, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 324 76 63 63 127 191 319), lower := (rows 35 131 324 76 16 32 64 128 256), losses := [] }

theorem u42922 : Upper (D 6) (R 6) [34,129,320,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42923_3 : Upper (D 6) (R 6) [34,129,320,80,3] 13 :=
  permutation_upper _ _ _ [34,129,320,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37466

theorem m42923_5 : Upper (D 6) (R 6) [34,129,320,80,5] 13 :=
  permutation_upper _ _ _ [34,129,320,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37476

theorem m42923_6 : Upper (D 6) (R 6) [34,129,320,80,6] 13 :=
  permutation_upper _ _ _ [34,129,320,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37485

theorem m42923_9 : Upper (D 6) (R 6) [34,129,320,80,9] 13 :=
  permutation_upper _ _ _ [34,129,320,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37494

theorem m42923_10 : Upper (D 6) (R 6) [34,129,320,80,10] 13 :=
  permutation_upper _ _ _ [34,129,320,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37502

theorem m42923_12 : Upper (D 6) (R 6) [34,129,320,80,12] 13 :=
  permutation_upper _ _ _ [34,129,320,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37512

theorem m42923_33 : Upper (D 6) (R 6) [34,129,320,80,33] 13 :=
  permutation_upper _ _ _ [34,129,320,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37515

theorem m42923_34 : Upper (D 6) (R 6) [34,129,320,80,34] 13 :=
  permutation_upper _ _ _ [34,129,320,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37517

theorem m42923_36 : Upper (D 6) (R 6) [34,129,320,80,36] 13 :=
  permutation_upper _ _ _ [34,129,320,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37521

theorem m42923_40 : Upper (D 6) (R 6) [34,129,320,80,40] 13 :=
  permutation_upper _ _ _ [34,129,320,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37525

def r42923 : Route 9 := (fun mask => (mask,id))

def c42923 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42923 : Upper (D 6) (R 6) [34,129,320,80] 13 := by
  apply FastRouting.sound _ _ [34,129,320,80] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r42923 c42923
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42923_3
  · exact m42923_5
  · exact m42923_6
  · exact m42923_9
  · exact m42923_10
  · exact m42923_12
  · exact m42923_33
  · exact m42923_34
  · exact m42923_36
  · exact m42923_40

theorem m42924_3 : Upper (D 6) (R 6) [34,129,320,96,3] 13 :=
  permutation_upper _ _ _ [34,129,320,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37467

theorem m42924_5 : Upper (D 6) (R 6) [34,129,320,96,5] 13 :=
  permutation_upper _ _ _ [34,129,320,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37477

theorem m42924_6 : Upper (D 6) (R 6) [34,129,320,96,6] 13 :=
  permutation_upper _ _ _ [34,129,320,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37486

theorem m42924_9 : Upper (D 6) (R 6) [34,129,320,96,9] 13 :=
  permutation_upper _ _ _ [34,129,320,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37495

theorem m42924_10 : Upper (D 6) (R 6) [34,129,320,96,10] 13 :=
  permutation_upper _ _ _ [34,129,320,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37503

theorem m42924_12 : Upper (D 6) (R 6) [34,129,320,96,12] 13 :=
  permutation_upper _ _ _ [34,129,320,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u37513

def r42924 : Route 9 := (fun mask => (mask,id))

def c42924 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42924 : Upper (D 6) (R 6) [34,129,320,96] 13 := by
  apply FastRouting.sound _ _ [34,129,320,96] 13 (by decide) (choices 2) [3,5,6,9,10,12] r42924 c42924
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42924_3
  · exact m42924_5
  · exact m42924_6
  · exact m42924_9
  · exact m42924_10
  · exact m42924_12

def b42925 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 8, targets := 36 },{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6),(3,2),(3,5)], upper := (rows 35 134 44 11 341 373 341 469 341), lower := (rows 35 134 44 11 16 32 64 128 256), losses := [] }

theorem u42925 : Upper (D 6) (R 6) [34,132,40,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42925 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42926 : PairBound 9 := { available := 339, camps := [{ cop := 0, region := 12, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 134 44 13 339 371 339 467 339), lower := (rows 35 134 44 13 16 32 64 128 256), losses := [] }

theorem u42926 : Upper (D 6) (R 6) [34,132,40,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42927 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 44 14 337 369 337 465 337), lower := (rows 35 134 44 14 16 32 64 128 256), losses := [] }

theorem u42927 : Upper (D 6) (R 6) [34,132,40,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42928 : Route 9 := (fun mask => (mask,id))

def c42928 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42928 : Upper (D 6) (R 6) [34,132,40,17] 13 := by
  apply FastRouting.sound _ _ [34,132,40,17] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42928 c42928
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37526
  · exact u37527
  · exact u37528
  · exact u37529
  · exact u37530
  · exact u37531
  · exact u37532
  · exact u37533
  · exact u37534
  · exact u37535

def r42929 : Route 9 := (fun mask => (mask,id))

def c42929 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42929 : Upper (D 6) (R 6) [34,132,40,18] 13 := by
  apply FastRouting.sound _ _ [34,132,40,18] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42929 c42929
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37536
  · exact u37537
  · exact u37538
  · exact u37539
  · exact u37540
  · exact u37541

def b42930 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 44 28 339 355 323 451 323), lower := (rows 35 134 44 28 16 32 64 128 256), losses := [] }

theorem u42930 : Upper (D 6) (R 6) [34,132,40,20] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42931 : Route 9 := (fun mask => (mask,id))

def c42931 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42931 : Upper (D 6) (R 6) [34,132,40,65] 13 := by
  apply FastRouting.sound _ _ [34,132,40,65] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42931 c42931
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37542
  · exact u37543
  · exact u37544
  · exact u37545
  · exact u37546
  · exact u37547
  · exact u37548
  · exact u37549
  · exact u37550
  · exact u37551

def r42932 : Route 9 := (fun mask => (mask,id))

def c42932 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42932 : Upper (D 6) (R 6) [34,132,40,66] 13 := by
  apply FastRouting.sound _ _ [34,132,40,66] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42932 c42932
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37552
  · exact u37553
  · exact u37554
  · exact u37555
  · exact u37556
  · exact u37557

def b42933 : PairBound 9 := { available := 339, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 44 76 339 371 339 467 339), lower := (rows 35 134 44 76 16 32 64 128 256), losses := [] }

theorem u42933 : Upper (D 6) (R 6) [34,132,40,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42934 : Route 9 := (fun mask => (mask,id))

def c42934 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42934 : Upper (D 6) (R 6) [34,132,40,80] 13 := by
  apply FastRouting.sound _ _ [34,132,40,80] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42934 c42934
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37558
  · exact u37559
  · exact u37560
  · exact u37561
  · exact u37562
  · exact u37563
  · exact u37564
  · exact u37565
  · exact u37566
  · exact u37567

def r42935 : Route 9 := (fun mask => (mask,id))

def c42935 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42935 : Upper (D 6) (R 6) [34,132,40,257] 13 := by
  apply FastRouting.sound _ _ [34,132,40,257] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42935 c42935
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37568
  · exact u37569
  · exact u37570
  · exact u37571
  · exact u37572
  · exact u37573

def r42936 : Route 9 := (fun mask => (mask,id))

def c42936 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42936 : Upper (D 6) (R 6) [34,132,40,258] 13 := by
  apply FastRouting.sound _ _ [34,132,40,258] 13 (by decide) (choices 2) [5,65,68] r42936 c42936
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u37574
  · exact u37575
  · exact u37576

def b42937 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 44 268 83 115 83 211 339), lower := (rows 35 134 44 268 16 32 64 128 256), losses := [] }

theorem u42937 : Upper (D 6) (R 6) [34,132,40,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42938 : Route 9 := (fun mask => (mask,id))

def c42938 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42938 : Upper (D 6) (R 6) [34,132,40,272] 13 := by
  apply FastRouting.sound _ _ [34,132,40,272] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42938 c42938
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37577
  · exact u37578
  · exact u37579
  · exact u37580
  · exact u37581
  · exact u37582

def r42939 : Route 9 := (fun mask => (mask,id))

def c42939 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42939 : Upper (D 6) (R 6) [34,132,40,320] 13 := by
  apply FastRouting.sound _ _ [34,132,40,320] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42939 c42939
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37583
  · exact u37584
  · exact u37585
  · exact u37586
  · exact u37587
  · exact u37588

def b42940 : PairBound 9 := { available := 373, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 134 76 11 373 373 373 501 373), lower := (rows 35 134 76 11 16 32 64 128 256), losses := [] }

theorem u42940 : Upper (D 6) (R 6) [34,132,72,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42941 : Route 9 := (fun mask => (mask,id))

def c42941 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42941 : Upper (D 6) (R 6) [34,132,72,5] 13 := by
  apply FastRouting.sound _ _ [34,132,72,5] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r42941 c42941
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37589
  · exact u37590
  · exact u37591
  · exact u37592
  · exact u37593
  · exact u37594
  · exact u37595
  · exact u37596
  · exact u37597
  · exact u37598

def b42942 : PairBound 9 := { available := 369, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 134 76 14 369 369 369 497 369), lower := (rows 35 134 76 14 16 32 64 128 256), losses := [] }

theorem u42942 : Upper (D 6) (R 6) [34,132,72,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42943 : Route 9 := (fun mask => (mask,id))

def c42943 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42943 : Upper (D 6) (R 6) [34,132,72,17] 13 := by
  apply FastRouting.sound _ _ [34,132,72,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r42943 c42943
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37599
  · exact u37600
  · exact u37601
  · exact u37602
  · exact u37603
  · exact u37604
  · exact u37605
  · exact u37606
  · exact u37607
  · exact u37608
  · exact u37609
  · exact u37610
  · exact u37611
  · exact u37612
  · exact u37613

def r42944 : Route 9 := (fun mask => (mask,id))

def c42944 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42944 : Upper (D 6) (R 6) [34,132,72,18] 13 := by
  apply FastRouting.sound _ _ [34,132,72,18] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r42944 c42944
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37614
  · exact u37615
  · exact u37616
  · exact u37617
  · exact u37618
  · exact u37619
  · exact u37620
  · exact u37621
  · exact u37622
  · exact u37623

def r42945 : Route 9 := (fun mask => (mask,id))

def c42945 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42945 : Upper (D 6) (R 6) [34,132,72,20] 13 := by
  apply FastRouting.sound _ _ [34,132,72,20] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r42945 c42945
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37624
  · exact u37625
  · exact u37626
  · exact u37627
  · exact u37628
  · exact u37629
  · exact u37630
  · exact u37631
  · exact u37632
  · exact u37633

def b42946 : PairBound 9 := { available := 343, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 134 76 41 343 375 343 471 343), lower := (rows 35 134 76 41 16 32 64 128 256), losses := [] }

theorem u42946 : Upper (D 6) (R 6) [34,132,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42947 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 134 76 42 341 373 341 469 341), lower := (rows 35 134 76 42 16 32 64 128 256), losses := [] }

theorem u42947 : Upper (D 6) (R 6) [34,132,72,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42948 : PairBound 9 := { available := 339, camps := [{ cop := 1, region := 369, targets := 4 },{ cop := 0, region := 336, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 76 44 339 371 339 467 339), lower := (rows 35 134 76 44 16 32 64 128 256), losses := [] }

theorem u42948 : Upper (D 6) (R 6) [34,132,72,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42949 : Route 9 := (fun mask => (mask,id))

def c42949 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42949 : Upper (D 6) (R 6) [34,132,72,48] 13 := by
  apply FastRouting.sound _ _ [34,132,72,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42949 c42949
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37634
  · exact u37635
  · exact u37636
  · exact u37637
  · exact u37638
  · exact u37639
  · exact u37640
  · exact u37641
  · exact u37642
  · exact u37643

def b42950 : PairBound 9 := { available := 311, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 76 73 311 311 375 439 311), lower := (rows 35 134 76 73 16 32 64 128 256), losses := [] }

theorem u42950 : Upper (D 6) (R 6) [34,132,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42951 : PairBound 9 := { available := 309, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 76 74 309 309 373 437 309), lower := (rows 35 134 76 74 16 32 64 128 256), losses := [] }

theorem u42951 : Upper (D 6) (R 6) [34,132,72,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42952 : PairBound 9 := { available := 307, camps := [{ cop := 6, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 35 134 76 76 307 307 371 435 307), lower := (rows 35 134 76 76 16 32 64 128 256), losses := [] }

theorem u42952 : Upper (D 6) (R 6) [34,132,72,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42953 : PairBound 9 := { available := 295, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 76 88 311 295 359 423 295), lower := (rows 35 134 76 88 16 32 64 128 256), losses := [] }

theorem u42953 : Upper (D 6) (R 6) [34,132,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42954 : PairBound 9 := { available := 279, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 76 104 279 311 343 407 279), lower := (rows 35 134 76 104 16 32 64 128 256), losses := [] }

theorem u42954 : Upper (D 6) (R 6) [34,132,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42955 : Route 9 := (fun mask => (mask,id))

def c42955 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42955 : Upper (D 6) (R 6) [34,132,72,257] 13 := by
  apply FastRouting.sound _ _ [34,132,72,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42955 c42955
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37644
  · exact u37645
  · exact u37646
  · exact u37647
  · exact u37648
  · exact u37649
  · exact u37650
  · exact u37651
  · exact u37652
  · exact u37653

def r42956 : Route 9 := (fun mask => (mask,id))

def c42956 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42956 : Upper (D 6) (R 6) [34,132,72,258] 13 := by
  apply FastRouting.sound _ _ [34,132,72,258] 13 (by decide) (choices 2) [5,33,36,65,68,96] r42956 c42956
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37654
  · exact u37655
  · exact u37656
  · exact u37657
  · exact u37658
  · exact u37659

def r42957 : Route 9 := (fun mask => (mask,id))

def c42957 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42957 : Upper (D 6) (R 6) [34,132,72,260] 13 := by
  apply FastRouting.sound _ _ [34,132,72,260] 13 (by decide) (choices 2) [3,33,34,65,66,96] r42957 c42957
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37660
  · exact u37661
  · exact u37662
  · exact u37663
  · exact u37664
  · exact u37665

def r42958 : Route 9 := (fun mask => (mask,id))

def c42958 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42958 : Upper (D 6) (R 6) [34,132,72,272] 13 := by
  apply FastRouting.sound _ _ [34,132,72,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42958 c42958
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37666
  · exact u37667
  · exact u37668
  · exact u37669
  · exact u37670
  · exact u37671
  · exact u37672
  · exact u37673
  · exact u37674
  · exact u37675

def r42959 : Route 9 := (fun mask => (mask,id))

def c42959 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42959 : Upper (D 6) (R 6) [34,132,72,288] 13 := by
  apply FastRouting.sound _ _ [34,132,72,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42959 c42959
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u37676
  · exact u37677
  · exact u37678
  · exact u37679
  · exact u37680
  · exact u37681

#print axioms u42959
end Delivery.IrregularNine14.P06
