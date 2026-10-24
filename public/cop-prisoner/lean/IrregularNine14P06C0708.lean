import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0591
import IrregularNine14P06C0592
import IrregularNine14P06C0593
import IrregularNine14P06C0594
import IrregularNine14P06C0595

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m42480_3 : Upper (D 6) (R 6) [24,132,288,96,3] 13 :=
  permutation_upper _ _ _ [24,132,288,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35467

theorem m42480_5 : Upper (D 6) (R 6) [24,132,288,96,5] 13 :=
  permutation_upper _ _ _ [24,132,288,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35472

theorem m42480_6 : Upper (D 6) (R 6) [24,132,288,96,6] 13 :=
  permutation_upper _ _ _ [24,132,288,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35477

theorem m42480_65 : Upper (D 6) (R 6) [24,132,288,96,65] 13 :=
  permutation_upper _ _ _ [24,132,288,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35489

theorem m42480_66 : Upper (D 6) (R 6) [24,132,288,96,66] 13 :=
  permutation_upper _ _ _ [24,132,288,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35492

theorem m42480_68 : Upper (D 6) (R 6) [24,132,288,96,68] 13 :=
  permutation_upper _ _ _ [24,132,288,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35493

def r42480 : Route 9 := (fun mask => (mask,id))

def c42480 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42480 : Upper (D 6) (R 6) [24,132,288,96] 13 := by
  apply FastRouting.sound _ _ [24,132,288,96] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42480 c42480
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42480_3
  · exact m42480_5
  · exact m42480_6
  · exact m42480_65
  · exact m42480_66
  · exact m42480_68

def r42481 : Route 9 := (fun mask => (mask,id))

def c42481 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42481 : Upper (D 6) (R 6) [24,160,288,3] 13 := by
  apply FastRouting.sound _ _ [24,160,288,3] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42481 c42481
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35494
  · exact u35495
  · exact u35496
  · exact u35497
  · exact u35498
  · exact u35499

theorem m42482_3 : Upper (D 6) (R 6) [24,160,288,6,3] 13 :=
  permutation_upper _ _ _ [24,160,288,3,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35496

theorem m42482_5 : Upper (D 6) (R 6) [24,160,288,6,5] 13 :=
  permutation_upper _ _ _ [24,160,288,3,6] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35496

theorem m42482_68 : Upper (D 6) (R 6) [24,160,288,6,68] 13 :=
  permutation_upper _ _ _ [24,160,288,6,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35502

def r42482 : Route 9 := (fun mask => (mask,id))

def c42482 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42482 : Upper (D 6) (R 6) [24,160,288,6] 13 := by
  apply FastRouting.sound _ _ [24,160,288,6] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42482 c42482
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42482_3
  · exact m42482_5
  · exact u35500
  · exact u35501
  · exact u35502
  · exact m42482_68

theorem m42483_3 : Upper (D 6) (R 6) [24,160,288,65,3] 13 :=
  permutation_upper _ _ _ [24,160,288,3,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35497

theorem m42483_5 : Upper (D 6) (R 6) [24,160,288,65,5] 13 :=
  permutation_upper _ _ _ [24,160,288,3,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35497

theorem m42483_6 : Upper (D 6) (R 6) [24,160,288,65,6] 13 :=
  permutation_upper _ _ _ [24,160,288,6,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35501

theorem m42483_68 : Upper (D 6) (R 6) [24,160,288,65,68] 13 :=
  permutation_upper _ _ _ [24,160,288,65,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35504

def r42483 : Route 9 := (fun mask => (mask,id))

def c42483 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42483 : Upper (D 6) (R 6) [24,160,288,65] 13 := by
  apply FastRouting.sound _ _ [24,160,288,65] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42483 c42483
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42483_3
  · exact m42483_5
  · exact m42483_6
  · exact u35503
  · exact u35504
  · exact m42483_68

theorem m42484_3 : Upper (D 6) (R 6) [24,160,288,66,3] 13 :=
  permutation_upper _ _ _ [24,160,288,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35498

theorem m42484_5 : Upper (D 6) (R 6) [24,160,288,66,5] 13 :=
  permutation_upper _ _ _ [24,160,288,3,68] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35499

theorem m42484_6 : Upper (D 6) (R 6) [24,160,288,66,6] 13 :=
  permutation_upper _ _ _ [24,160,288,6,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35502

theorem m42484_65 : Upper (D 6) (R 6) [24,160,288,66,65] 13 :=
  permutation_upper _ _ _ [24,160,288,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35504

def r42484 : Route 9 := (fun mask => (mask,id))

def c42484 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42484 : Upper (D 6) (R 6) [24,160,288,66] 13 := by
  apply FastRouting.sound _ _ [24,160,288,66] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42484 c42484
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42484_3
  · exact m42484_5
  · exact m42484_6
  · exact m42484_65
  · exact u35505
  · exact u35506

def r42485 : Route 9 := (fun mask => (mask,id))

def c42485 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42485 : Upper (D 6) (R 6) [24,160,320,3] 13 := by
  apply FastRouting.sound _ _ [24,160,320,3] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42485 c42485
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35507
  · exact u35508
  · exact u35509
  · exact u35510
  · exact u35511
  · exact u35512
  · exact u35513
  · exact u35514
  · exact u35515
  · exact u35516

theorem m42486_3 : Upper (D 6) (R 6) [24,160,320,6,3] 13 :=
  permutation_upper _ _ _ [24,160,320,3,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35509

theorem m42486_5 : Upper (D 6) (R 6) [24,160,320,6,5] 13 :=
  permutation_upper _ _ _ [24,160,320,3,6] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35509

theorem m42486_65 : Upper (D 6) (R 6) [24,160,320,6,65] 13 :=
  permutation_upper _ _ _ [24,160,320,6,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35518

theorem m42486_66 : Upper (D 6) (R 6) [24,160,320,6,66] 13 :=
  permutation_upper _ _ _ [24,160,320,6,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35520

theorem m42486_68 : Upper (D 6) (R 6) [24,160,320,6,68] 13 :=
  permutation_upper _ _ _ [24,160,320,6,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35519

def r42486 : Route 9 := (fun mask => (mask,id))

def c42486 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42486 : Upper (D 6) (R 6) [24,160,320,6] 13 := by
  apply FastRouting.sound _ _ [24,160,320,6] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r42486 c42486
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42486_3
  · exact m42486_5
  · exact u35517
  · exact u35518
  · exact u35519
  · exact u35520
  · exact m42486_65
  · exact m42486_66
  · exact m42486_68
  · exact u35521

theorem m42487_3 : Upper (D 6) (R 6) [24,160,320,33,3] 13 :=
  permutation_upper _ _ _ [24,160,320,3,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35510

theorem m42487_5 : Upper (D 6) (R 6) [24,160,320,33,5] 13 :=
  permutation_upper _ _ _ [24,160,320,3,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35513

theorem m42487_6 : Upper (D 6) (R 6) [24,160,320,33,6] 13 :=
  permutation_upper _ _ _ [24,160,320,6,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35518

def r42487 : Route 9 := (fun mask => (mask,id))

def c42487 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42487 : Upper (D 6) (R 6) [24,160,320,33] 13 := by
  apply FastRouting.sound _ _ [24,160,320,33] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42487 c42487
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42487_3
  · exact m42487_5
  · exact m42487_6
  · exact u35522
  · exact u35523
  · exact u35524

def b42488 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 162 324 42 87 103 71 199 327), lower := (rows 25 162 324 42 16 32 64 128 256), losses := [] }

theorem u42488 : Upper (D 6) (R 6) [24,160,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42489_3 : Upper (D 6) (R 6) [24,160,320,36,3] 13 :=
  permutation_upper _ _ _ [24,160,320,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35512

theorem m42489_5 : Upper (D 6) (R 6) [24,160,320,36,5] 13 :=
  permutation_upper _ _ _ [24,160,320,3,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35514

theorem m42489_6 : Upper (D 6) (R 6) [24,160,320,36,6] 13 :=
  permutation_upper _ _ _ [24,160,320,6,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35520

theorem m42489_65 : Upper (D 6) (R 6) [24,160,320,36,65] 13 :=
  permutation_upper _ _ _ [24,160,320,33,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35523

theorem m42489_68 : Upper (D 6) (R 6) [24,160,320,36,68] 13 :=
  permutation_upper _ _ _ [24,160,320,34,66] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35525

def r42489 : Route 9 := (fun mask => (mask,id))

def c42489 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42489 : Upper (D 6) (R 6) [24,160,320,36] 13 := by
  apply FastRouting.sound _ _ [24,160,320,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42489 c42489
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42489_3
  · exact m42489_5
  · exact m42489_6
  · exact m42489_65
  · exact u35526
  · exact m42489_68

theorem m42490_3 : Upper (D 6) (R 6) [24,160,320,96,3] 13 :=
  permutation_upper _ _ _ [24,160,320,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35516

theorem m42490_5 : Upper (D 6) (R 6) [24,160,320,96,5] 13 :=
  permutation_upper _ _ _ [24,160,320,3,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35516

theorem m42490_6 : Upper (D 6) (R 6) [24,160,320,96,6] 13 :=
  permutation_upper _ _ _ [24,160,320,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35521

def r42490 : Route 9 := (fun mask => (mask,id))

def c42490 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42490 : Upper (D 6) (R 6) [24,160,320,96] 13 := by
  apply FastRouting.sound _ _ [24,160,320,96] 13 (by decide) (choices 2) [3,5,6] r42490 c42490
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m42490_3
  · exact m42490_5
  · exact m42490_6

def b42491 : PairBound 9 := { available := 468, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 44 11 468 500 468 468 468), lower := (rows 35 67 44 11 16 32 64 128 256), losses := [] }

theorem u42491 : Upper (D 6) (R 6) [34,65,40,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42492 : PairBound 9 := { available := 470, camps := [{ cop := 0, region := 12, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 67 44 13 470 502 470 470 470), lower := (rows 35 67 44 13 16 32 64 128 256), losses := [] }

theorem u42492 : Upper (D 6) (R 6) [34,65,40,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42493 : PairBound 9 := { available := 469, camps := [{ cop := 0, region := 12, targets := 1 },{ cop := 0, region := 12, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 35 67 44 14 469 501 469 469 469), lower := (rows 35 67 44 14 16 32 64 128 256), losses := [] }

theorem u42493 : Upper (D 6) (R 6) [34,65,40,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42494 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42494 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42494 : Upper (D 6) (R 6) [34,65,40,17] 13 := by
  apply FastRouting.sound _ _ [34,65,40,17] 13 (by decide) (choices 2) [6,66,68,130,132,192,384] r42494 c42494
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35527
  · exact u35528
  · exact u35529
  · exact u35530
  · exact u35531
  · exact u35532
  · exact u35533

def r42495 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42495 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42495 : Upper (D 6) (R 6) [34,65,40,18] 13 := by
  apply FastRouting.sound _ _ [34,65,40,18] 13 (by decide) (choices 2) [5,65,68,129,132,192,384] r42495 c42495
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35534
  · exact u35535
  · exact u35536
  · exact u35537
  · exact u35538
  · exact u35539
  · exact u35540

def r42496 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42496 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u42496 : Upper (D 6) (R 6) [34,65,40,20] 13 := by
  apply FastRouting.sound _ _ [34,65,40,20] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r42496 c42496
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35541
  · exact u35542
  · exact u35543
  · exact u35544
  · exact u35545
  · exact u35546
  · exact u35547
  · exact u35548
  · exact u35549
  · exact u35550
  · exact u35551

def b42497 : PairBound 9 := { available := 406, camps := [{ cop := 1, region := 8, targets := 36 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,5)], upper := (rows 35 67 44 73 406 438 470 406 406), lower := (rows 35 67 44 73 16 32 64 128 256), losses := [] }

theorem u42497 : Upper (D 6) (R 6) [34,65,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42498 : PairBound 9 := { available := 405, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 67 44 74 405 437 469 405 405), lower := (rows 35 67 44 74 16 32 64 128 256), losses := [] }

theorem u42498 : Upper (D 6) (R 6) [34,65,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42499 : PairBound 9 := { available := 407, camps := [], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 44 76 407 439 471 407 407), lower := (rows 35 67 44 76 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 10 16 32 64 128 256), good := (rows 46 78 44 76 16 32 64 128 256) },{ target := 1, region := (rows 1 0 5 10 16 32 64 128 256), good := (rows 45 77 44 76 16 32 64 128 256) }] }

theorem u42499 : Upper (D 6) (R 6) [34,65,40,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42500 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42500 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42500 : Upper (D 6) (R 6) [34,65,40,80] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r42500 c42500
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35552
  · exact u35553
  · exact u35554
  · exact u35555
  · exact u35556
  · exact u35557
  · exact u35558

def r42501 : Route 9 := (fun mask => (mask,id))

def c42501 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42501 : Upper (D 6) (R 6) [34,65,40,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129] 13 (by decide) (choices 2) [6,66,68,258,260,320] r42501 c42501
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35559
  · exact u35560
  · exact u35561
  · exact u35562
  · exact u35563
  · exact u35564

def r42502 : Route 9 := (fun mask => (mask,id))

def c42502 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42502 : Upper (D 6) (R 6) [34,65,40,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130] 13 (by decide) (choices 2) [5,65,68,257,260,320] r42502 c42502
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35565
  · exact u35566
  · exact u35567
  · exact u35568
  · exact u35569
  · exact u35570

def r42503 : Route 9 := (fun mask => (mask,id))

def c42503 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42503 : Upper (D 6) (R 6) [34,65,40,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42503 c42503
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35571
  · exact u35572
  · exact u35573
  · exact u35574
  · exact u35575
  · exact u35576
  · exact u35577
  · exact u35578
  · exact u35579
  · exact u35580

def r42504 : Route 9 := (fun mask => (mask,id))

def c42504 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42504 : Upper (D 6) (R 6) [34,65,40,144] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42504 c42504
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35581
  · exact u35582
  · exact u35583
  · exact u35584
  · exact u35585
  · exact u35586
  · exact u35587
  · exact u35588
  · exact u35589
  · exact u35590

def r42505 : Route 9 := (fun mask => (mask,id))

def c42505 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42505 : Upper (D 6) (R 6) [34,65,40,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42505 c42505
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35591
  · exact u35592
  · exact u35593
  · exact u35594
  · exact u35595
  · exact u35596

def r42506 : Route 9 := (fun mask => (mask,id))

def c42506 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42506 : Upper (D 6) (R 6) [34,65,40,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r42506 c42506
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35597
  · exact u35598
  · exact u35599
  · exact u35600
  · exact u35601
  · exact u35602

def b42507 : PairBound 9 := { available := 412, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 100 11 412 444 476 412 412), lower := (rows 35 67 100 11 16 32 64 128 256), losses := [] }

theorem u42507 : Upper (D 6) (R 6) [34,65,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42508 : PairBound 9 := { available := 414, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 3, region := 466, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 67 100 13 414 446 478 414 414), lower := (rows 35 67 100 13 16 32 64 128 256), losses := [] }

theorem u42508 : Upper (D 6) (R 6) [34,65,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42509_6 : Upper (D 6) (R 6) [34,65,96,17,6] 13 :=
  permutation_upper _ _ _ [34,65,96,5,10] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35607

def r42509 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42509 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42509 : Upper (D 6) (R 6) [34,65,96,17] 13 := by
  apply FastRouting.sound _ _ [34,65,96,17] 13 (by decide) (choices 2) [6,10,12,130,132,136,384] r42509 c42509
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42509_6
  · exact u35613
  · exact u35614
  · exact u35615
  · exact u35616
  · exact u35617
  · exact u35618

theorem m42510_3 : Upper (D 6) (R 6) [34,65,96,20,3] 13 :=
  permutation_upper _ _ _ [34,65,96,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35603

theorem m42510_5 : Upper (D 6) (R 6) [34,65,96,20,5] 13 :=
  permutation_upper _ _ _ [34,65,96,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35608

theorem m42510_6 : Upper (D 6) (R 6) [34,65,96,20,6] 13 :=
  permutation_upper _ _ _ [34,65,96,5,12] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35608

theorem m42510_9 : Upper (D 6) (R 6) [34,65,96,20,9] 13 :=
  permutation_upper _ _ _ [34,65,96,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35614

theorem m42510_10 : Upper (D 6) (R 6) [34,65,96,20,10] 13 :=
  permutation_upper _ _ _ [34,65,96,17,12] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35614

theorem m42510_130 : Upper (D 6) (R 6) [34,65,96,20,130] 13 :=
  permutation_upper _ _ _ [34,65,96,20,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35620

def r42510 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c42510 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u42510 : Upper (D 6) (R 6) [34,65,96,20] 13 := by
  apply FastRouting.sound _ _ [34,65,96,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,384] r42510 c42510
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42510_3
  · exact m42510_5
  · exact m42510_6
  · exact m42510_9
  · exact m42510_10
  · exact u35619
  · exact u35620
  · exact m42510_130
  · exact u35621
  · exact u35622
  · exact u35623

theorem m42511_6 : Upper (D 6) (R 6) [34,65,96,129,6] 13 :=
  permutation_upper _ _ _ [34,65,96,5,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35609

theorem m42511_10 : Upper (D 6) (R 6) [34,65,96,129,10] 13 :=
  permutation_upper _ _ _ [34,65,96,17,130] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35615

theorem m42511_12 : Upper (D 6) (R 6) [34,65,96,129,12] 13 :=
  permutation_upper _ _ _ [34,65,96,20,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35620

def r42511 : Route 9 := (fun mask => (mask,id))

def c42511 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42511 : Upper (D 6) (R 6) [34,65,96,129] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129] 13 (by decide) (choices 2) [6,10,12,258,260,264] r42511 c42511
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42511_6
  · exact m42511_10
  · exact m42511_12
  · exact u35624
  · exact u35625
  · exact u35626

theorem m42512_3 : Upper (D 6) (R 6) [34,65,96,132,3] 13 :=
  permutation_upper _ _ _ [34,65,96,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35604

theorem m42512_5 : Upper (D 6) (R 6) [34,65,96,132,5] 13 :=
  permutation_upper _ _ _ [34,65,96,5,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35610

theorem m42512_6 : Upper (D 6) (R 6) [34,65,96,132,6] 13 :=
  permutation_upper _ _ _ [34,65,96,5,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35610

theorem m42512_9 : Upper (D 6) (R 6) [34,65,96,132,9] 13 :=
  permutation_upper _ _ _ [34,65,96,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35616

theorem m42512_10 : Upper (D 6) (R 6) [34,65,96,132,10] 13 :=
  permutation_upper _ _ _ [34,65,96,17,132] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35616

theorem m42512_12 : Upper (D 6) (R 6) [34,65,96,132,12] 13 :=
  permutation_upper _ _ _ [34,65,96,20,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35621

theorem m42512_257 : Upper (D 6) (R 6) [34,65,96,132,257] 13 :=
  permutation_upper _ _ _ [34,65,96,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35625

theorem m42512_258 : Upper (D 6) (R 6) [34,65,96,132,258] 13 :=
  permutation_upper _ _ _ [34,65,96,129,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35625

def r42512 : Route 9 := (fun mask => (mask,id))

def c42512 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42512 : Upper (D 6) (R 6) [34,65,96,132] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r42512 c42512
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42512_3
  · exact m42512_5
  · exact m42512_6
  · exact m42512_9
  · exact m42512_10
  · exact m42512_12
  · exact m42512_257
  · exact m42512_258
  · exact u35627
  · exact u35628

theorem m42513_3 : Upper (D 6) (R 6) [34,65,96,144,3] 13 :=
  permutation_upper _ _ _ [34,65,96,3,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35605

theorem m42513_5 : Upper (D 6) (R 6) [34,65,96,144,5] 13 :=
  permutation_upper _ _ _ [34,65,96,5,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35611

theorem m42513_6 : Upper (D 6) (R 6) [34,65,96,144,6] 13 :=
  permutation_upper _ _ _ [34,65,96,5,136] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35611

theorem m42513_9 : Upper (D 6) (R 6) [34,65,96,144,9] 13 :=
  permutation_upper _ _ _ [34,65,96,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35617

theorem m42513_10 : Upper (D 6) (R 6) [34,65,96,144,10] 13 :=
  permutation_upper _ _ _ [34,65,96,17,136] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35617

theorem m42513_12 : Upper (D 6) (R 6) [34,65,96,144,12] 13 :=
  permutation_upper _ _ _ [34,65,96,20,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35622

theorem m42513_257 : Upper (D 6) (R 6) [34,65,96,144,257] 13 :=
  permutation_upper _ _ _ [34,65,96,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35626

theorem m42513_258 : Upper (D 6) (R 6) [34,65,96,144,258] 13 :=
  permutation_upper _ _ _ [34,65,96,129,264] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35626

theorem m42513_260 : Upper (D 6) (R 6) [34,65,96,144,260] 13 :=
  permutation_upper _ _ _ [34,65,96,132,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35628

def r42513 : Route 9 := (fun mask => (mask,id))

def c42513 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42513 : Upper (D 6) (R 6) [34,65,96,144] 13 := by
  apply FastRouting.sound _ _ [34,65,96,144] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r42513 c42513
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42513_3
  · exact m42513_5
  · exact m42513_6
  · exact m42513_9
  · exact m42513_10
  · exact m42513_12
  · exact m42513_257
  · exact m42513_258
  · exact m42513_260
  · exact u35629

theorem m42514_3 : Upper (D 6) (R 6) [34,65,96,384,3] 13 :=
  permutation_upper _ _ _ [34,65,96,3,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35606

theorem m42514_5 : Upper (D 6) (R 6) [34,65,96,384,5] 13 :=
  permutation_upper _ _ _ [34,65,96,5,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35612

theorem m42514_6 : Upper (D 6) (R 6) [34,65,96,384,6] 13 :=
  permutation_upper _ _ _ [34,65,96,5,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35612

theorem m42514_9 : Upper (D 6) (R 6) [34,65,96,384,9] 13 :=
  permutation_upper _ _ _ [34,65,96,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35618

theorem m42514_10 : Upper (D 6) (R 6) [34,65,96,384,10] 13 :=
  permutation_upper _ _ _ [34,65,96,17,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35618

theorem m42514_12 : Upper (D 6) (R 6) [34,65,96,384,12] 13 :=
  permutation_upper _ _ _ [34,65,96,20,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35623

def r42514 : Route 9 := (fun mask => (mask,id))

def c42514 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42514 : Upper (D 6) (R 6) [34,65,96,384] 13 := by
  apply FastRouting.sound _ _ [34,65,96,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r42514 c42514
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42514_3
  · exact m42514_5
  · exact m42514_6
  · exact m42514_9
  · exact m42514_10
  · exact m42514_12

def r42515 : Route 9 := (fun mask => (mask,id))

def c42515 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42515 : Upper (D 6) (R 6) [34,65,129,6] 13 := by
  apply FastRouting.sound _ _ [34,65,129,6] 13 (by decide) (choices 2) [12,36,40,68,72,96,260,264,288,320] r42515 c42515
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35630
  · exact u35631
  · exact u35632
  · exact u35633
  · exact u35634
  · exact u35635
  · exact u35636
  · exact u35637
  · exact u35638
  · exact u35639

def r42516 : Route 9 := (fun mask => (mask,id))

def c42516 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42516 : Upper (D 6) (R 6) [34,65,129,18] 13 := by
  apply FastRouting.sound _ _ [34,65,129,18] 13 (by decide) (choices 2) [12,36,40,68,72,96,260,264,288,320] r42516 c42516
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35640
  · exact u35641
  · exact u35642
  · exact u35643
  · exact u35644
  · exact u35645
  · exact u35646
  · exact u35647
  · exact u35648
  · exact u35649

theorem m42517_6 : Upper (D 6) (R 6) [34,65,129,20,6] 13 :=
  permutation_upper _ _ _ [34,65,129,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35630

theorem m42517_10 : Upper (D 6) (R 6) [34,65,129,20,10] 13 :=
  permutation_upper _ _ _ [34,65,129,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35640

def r42517 : Route 9 := (fun mask => (mask,id))

def c42517 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42517 : Upper (D 6) (R 6) [34,65,129,20] 13 := by
  apply FastRouting.sound _ _ [34,65,129,20] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96,258,260,264,288,320] r42517 c42517
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42517_6
  · exact m42517_10
  · exact u35650
  · exact u35651
  · exact u35652
  · exact u35653
  · exact u35654
  · exact u35655
  · exact u35656
  · exact u35657
  · exact u35658
  · exact u35659
  · exact u35660
  · exact u35661
  · exact u35662

def b42518 : PairBound 9 := { available := 348, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 67 133 42 348 380 348 476 348), lower := (rows 35 67 133 42 16 32 64 128 256), losses := [] }

theorem u42518 : Upper (D 6) (R 6) [34,65,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42519_6 : Upper (D 6) (R 6) [34,65,129,36,6] 13 :=
  permutation_upper _ _ _ [34,65,129,6,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35631

theorem m42519_10 : Upper (D 6) (R 6) [34,65,129,36,10] 13 :=
  permutation_upper _ _ _ [34,65,129,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35641

theorem m42519_12 : Upper (D 6) (R 6) [34,65,129,36,12] 13 :=
  permutation_upper _ _ _ [34,65,129,20,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35652

def r42519 : Route 9 := (fun mask => (mask,id))

def c42519 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42519 : Upper (D 6) (R 6) [34,65,129,36] 13 := by
  apply FastRouting.sound _ _ [34,65,129,36] 13 (by decide) (choices 2) [6,10,12,66,68,72,258,260,264,320] r42519 c42519
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42519_6
  · exact m42519_10
  · exact m42519_12
  · exact u35668
  · exact u35669
  · exact u35670
  · exact u35671
  · exact u35672
  · exact u35673
  · exact u35674

theorem m42520_6 : Upper (D 6) (R 6) [34,65,129,48,6] 13 :=
  permutation_upper _ _ _ [34,65,129,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35632

theorem m42520_10 : Upper (D 6) (R 6) [34,65,129,48,10] 13 :=
  permutation_upper _ _ _ [34,65,129,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35642

theorem m42520_12 : Upper (D 6) (R 6) [34,65,129,48,12] 13 :=
  permutation_upper _ _ _ [34,65,129,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35653

def r42520 : Route 9 := (fun mask => (mask,id))

def c42520 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42520 : Upper (D 6) (R 6) [34,65,129,48] 13 := by
  apply FastRouting.sound _ _ [34,65,129,48] 13 (by decide) (choices 2) [6,10,12,66,68,72,258,260,264,320] r42520 c42520
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42520_6
  · exact m42520_10
  · exact m42520_12
  · exact u35675
  · exact u35676
  · exact u35677
  · exact u35678
  · exact u35679
  · exact u35680
  · exact u35681

def b42521 : PairBound 9 := { available := 316, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 67 133 74 316 316 380 444 316), lower := (rows 35 67 133 74 16 32 64 128 256), losses := [] }

theorem u42521 : Upper (D 6) (R 6) [34,65,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m42522_6 : Upper (D 6) (R 6) [34,65,129,68,6] 13 :=
  permutation_upper _ _ _ [34,65,129,6,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35633

theorem m42522_10 : Upper (D 6) (R 6) [34,65,129,68,10] 13 :=
  permutation_upper _ _ _ [34,65,129,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35643

theorem m42522_12 : Upper (D 6) (R 6) [34,65,129,68,12] 13 :=
  permutation_upper _ _ _ [34,65,129,20,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35655

theorem m42522_34 : Upper (D 6) (R 6) [34,65,129,68,34] 13 :=
  permutation_upper _ _ _ [34,65,129,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35663

theorem m42522_36 : Upper (D 6) (R 6) [34,65,129,68,36] 13 :=
  permutation_upper _ _ _ [34,65,129,36,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35669

theorem m42522_40 : Upper (D 6) (R 6) [34,65,129,68,40] 13 :=
  permutation_upper _ _ _ [34,65,129,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35676

def r42522 : Route 9 := (fun mask => (mask,id))

def c42522 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42522 : Upper (D 6) (R 6) [34,65,129,68] 13 := by
  apply FastRouting.sound _ _ [34,65,129,68] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r42522 c42522
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42522_6
  · exact m42522_10
  · exact m42522_12
  · exact m42522_34
  · exact m42522_36
  · exact m42522_40
  · exact u35685
  · exact u35686
  · exact u35687
  · exact u35688

theorem m42523_6 : Upper (D 6) (R 6) [34,65,129,80,6] 13 :=
  permutation_upper _ _ _ [34,65,129,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35634

theorem m42523_10 : Upper (D 6) (R 6) [34,65,129,80,10] 13 :=
  permutation_upper _ _ _ [34,65,129,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35644

theorem m42523_12 : Upper (D 6) (R 6) [34,65,129,80,12] 13 :=
  permutation_upper _ _ _ [34,65,129,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35656

theorem m42523_34 : Upper (D 6) (R 6) [34,65,129,80,34] 13 :=
  permutation_upper _ _ _ [34,65,129,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35664

theorem m42523_36 : Upper (D 6) (R 6) [34,65,129,80,36] 13 :=
  permutation_upper _ _ _ [34,65,129,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35670

theorem m42523_40 : Upper (D 6) (R 6) [34,65,129,80,40] 13 :=
  permutation_upper _ _ _ [34,65,129,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35677

def r42523 : Route 9 := (fun mask => (mask,id))

def c42523 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42523 : Upper (D 6) (R 6) [34,65,129,80] 13 := by
  apply FastRouting.sound _ _ [34,65,129,80] 13 (by decide) (choices 2) [6,10,12,34,36,40,258,260,264,288] r42523 c42523
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42523_6
  · exact m42523_10
  · exact m42523_12
  · exact m42523_34
  · exact m42523_36
  · exact m42523_40
  · exact u35689
  · exact u35690
  · exact u35691
  · exact u35692

theorem m42524_6 : Upper (D 6) (R 6) [34,65,129,96,6] 13 :=
  permutation_upper _ _ _ [34,65,129,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35635

theorem m42524_10 : Upper (D 6) (R 6) [34,65,129,96,10] 13 :=
  permutation_upper _ _ _ [34,65,129,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35645

theorem m42524_12 : Upper (D 6) (R 6) [34,65,129,96,12] 13 :=
  permutation_upper _ _ _ [34,65,129,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35657

def r42524 : Route 9 := (fun mask => (mask,id))

def c42524 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42524 : Upper (D 6) (R 6) [34,65,129,96] 13 := by
  apply FastRouting.sound _ _ [34,65,129,96] 13 (by decide) (choices 2) [6,10,12,258,260,264] r42524 c42524
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42524_6
  · exact m42524_10
  · exact m42524_12
  · exact u35693
  · exact u35694
  · exact u35695

theorem m42525_12 : Upper (D 6) (R 6) [34,65,129,258,12] 13 :=
  permutation_upper _ _ _ [34,65,129,20,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35658

theorem m42525_36 : Upper (D 6) (R 6) [34,65,129,258,36] 13 :=
  permutation_upper _ _ _ [34,65,129,36,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35671

theorem m42525_40 : Upper (D 6) (R 6) [34,65,129,258,40] 13 :=
  permutation_upper _ _ _ [34,65,129,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35678

theorem m42525_68 : Upper (D 6) (R 6) [34,65,129,258,68] 13 :=
  permutation_upper _ _ _ [34,65,129,68,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35685

theorem m42525_72 : Upper (D 6) (R 6) [34,65,129,258,72] 13 :=
  permutation_upper _ _ _ [34,65,129,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35689

theorem m42525_96 : Upper (D 6) (R 6) [34,65,129,258,96] 13 :=
  permutation_upper _ _ _ [34,65,129,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35693

def r42525 : Route 9 := (fun mask => (mask,id))

def c42525 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42525 : Upper (D 6) (R 6) [34,65,129,258] 13 := by
  apply FastRouting.sound _ _ [34,65,129,258] 13 (by decide) (choices 2) [12,36,40,68,72,96] r42525 c42525
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42525_12
  · exact m42525_36
  · exact m42525_40
  · exact m42525_68
  · exact m42525_72
  · exact m42525_96

theorem m42526_6 : Upper (D 6) (R 6) [34,65,129,260,6] 13 :=
  permutation_upper _ _ _ [34,65,129,6,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35636

theorem m42526_10 : Upper (D 6) (R 6) [34,65,129,260,10] 13 :=
  permutation_upper _ _ _ [34,65,129,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35646

theorem m42526_12 : Upper (D 6) (R 6) [34,65,129,260,12] 13 :=
  permutation_upper _ _ _ [34,65,129,20,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35659

theorem m42526_34 : Upper (D 6) (R 6) [34,65,129,260,34] 13 :=
  permutation_upper _ _ _ [34,65,129,34,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35665

theorem m42526_36 : Upper (D 6) (R 6) [34,65,129,260,36] 13 :=
  permutation_upper _ _ _ [34,65,129,36,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35672

theorem m42526_40 : Upper (D 6) (R 6) [34,65,129,260,40] 13 :=
  permutation_upper _ _ _ [34,65,129,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35679

theorem m42526_66 : Upper (D 6) (R 6) [34,65,129,260,66] 13 :=
  permutation_upper _ _ _ [34,65,129,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35682

theorem m42526_68 : Upper (D 6) (R 6) [34,65,129,260,68] 13 :=
  permutation_upper _ _ _ [34,65,129,68,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35686

theorem m42526_72 : Upper (D 6) (R 6) [34,65,129,260,72] 13 :=
  permutation_upper _ _ _ [34,65,129,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35690

theorem m42526_96 : Upper (D 6) (R 6) [34,65,129,260,96] 13 :=
  permutation_upper _ _ _ [34,65,129,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35694

def r42526 : Route 9 := (fun mask => (mask,id))

def c42526 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42526 : Upper (D 6) (R 6) [34,65,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,260] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r42526 c42526
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42526_6
  · exact m42526_10
  · exact m42526_12
  · exact m42526_34
  · exact m42526_36
  · exact m42526_40
  · exact m42526_66
  · exact m42526_68
  · exact m42526_72
  · exact m42526_96

theorem m42527_6 : Upper (D 6) (R 6) [34,65,129,272,6] 13 :=
  permutation_upper _ _ _ [34,65,129,6,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35637

theorem m42527_10 : Upper (D 6) (R 6) [34,65,129,272,10] 13 :=
  permutation_upper _ _ _ [34,65,129,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35647

theorem m42527_12 : Upper (D 6) (R 6) [34,65,129,272,12] 13 :=
  permutation_upper _ _ _ [34,65,129,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35660

theorem m42527_34 : Upper (D 6) (R 6) [34,65,129,272,34] 13 :=
  permutation_upper _ _ _ [34,65,129,34,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35666

theorem m42527_36 : Upper (D 6) (R 6) [34,65,129,272,36] 13 :=
  permutation_upper _ _ _ [34,65,129,36,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35673

theorem m42527_40 : Upper (D 6) (R 6) [34,65,129,272,40] 13 :=
  permutation_upper _ _ _ [34,65,129,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35680

theorem m42527_66 : Upper (D 6) (R 6) [34,65,129,272,66] 13 :=
  permutation_upper _ _ _ [34,65,129,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35683

theorem m42527_68 : Upper (D 6) (R 6) [34,65,129,272,68] 13 :=
  permutation_upper _ _ _ [34,65,129,68,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35687

theorem m42527_72 : Upper (D 6) (R 6) [34,65,129,272,72] 13 :=
  permutation_upper _ _ _ [34,65,129,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35691

theorem m42527_96 : Upper (D 6) (R 6) [34,65,129,272,96] 13 :=
  permutation_upper _ _ _ [34,65,129,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35695

def r42527 : Route 9 := (fun mask => (mask,id))

def c42527 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42527 : Upper (D 6) (R 6) [34,65,129,272] 13 := by
  apply FastRouting.sound _ _ [34,65,129,272] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r42527 c42527
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42527_6
  · exact m42527_10
  · exact m42527_12
  · exact m42527_34
  · exact m42527_36
  · exact m42527_40
  · exact m42527_66
  · exact m42527_68
  · exact m42527_72
  · exact m42527_96

theorem m42528_6 : Upper (D 6) (R 6) [34,65,129,288,6] 13 :=
  permutation_upper _ _ _ [34,65,129,6,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35638

theorem m42528_10 : Upper (D 6) (R 6) [34,65,129,288,10] 13 :=
  permutation_upper _ _ _ [34,65,129,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35648

theorem m42528_12 : Upper (D 6) (R 6) [34,65,129,288,12] 13 :=
  permutation_upper _ _ _ [34,65,129,20,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35661

theorem m42528_66 : Upper (D 6) (R 6) [34,65,129,288,66] 13 :=
  permutation_upper _ _ _ [34,65,129,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35684

theorem m42528_68 : Upper (D 6) (R 6) [34,65,129,288,68] 13 :=
  permutation_upper _ _ _ [34,65,129,68,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35688

theorem m42528_72 : Upper (D 6) (R 6) [34,65,129,288,72] 13 :=
  permutation_upper _ _ _ [34,65,129,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35692

def r42528 : Route 9 := (fun mask => (mask,id))

def c42528 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42528 : Upper (D 6) (R 6) [34,65,129,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,288] 13 (by decide) (choices 2) [6,10,12,66,68,72] r42528 c42528
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42528_6
  · exact m42528_10
  · exact m42528_12
  · exact m42528_66
  · exact m42528_68
  · exact m42528_72

theorem m42529_6 : Upper (D 6) (R 6) [34,65,129,320,6] 13 :=
  permutation_upper _ _ _ [34,65,129,6,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35639

theorem m42529_10 : Upper (D 6) (R 6) [34,65,129,320,10] 13 :=
  permutation_upper _ _ _ [34,65,129,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35649

theorem m42529_12 : Upper (D 6) (R 6) [34,65,129,320,12] 13 :=
  permutation_upper _ _ _ [34,65,129,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35662

theorem m42529_34 : Upper (D 6) (R 6) [34,65,129,320,34] 13 :=
  permutation_upper _ _ _ [34,65,129,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35667

theorem m42529_36 : Upper (D 6) (R 6) [34,65,129,320,36] 13 :=
  permutation_upper _ _ _ [34,65,129,36,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35674

theorem m42529_40 : Upper (D 6) (R 6) [34,65,129,320,40] 13 :=
  permutation_upper _ _ _ [34,65,129,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35681

def r42529 : Route 9 := (fun mask => (mask,id))

def c42529 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42529 : Upper (D 6) (R 6) [34,65,129,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,320] 13 (by decide) (choices 2) [6,10,12,34,36,40] r42529 c42529
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m42529_6
  · exact m42529_10
  · exact m42529_12
  · exact m42529_34
  · exact m42529_36
  · exact m42529_40

def b42530 : PairBound 9 := { available := 372, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 140 11 372 372 372 500 372), lower := (rows 35 67 140 11 16 32 64 128 256), losses := [] }

theorem u42530 : Upper (D 6) (R 6) [34,65,136,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42531 : Route 9 := (fun mask => (mask,id))

def c42531 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42531 : Upper (D 6) (R 6) [34,65,136,5] 13 := by
  apply FastRouting.sound _ _ [34,65,136,5] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42531 c42531
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35696
  · exact u35697
  · exact u35698
  · exact u35699
  · exact u35700
  · exact u35701
  · exact u35702
  · exact u35703
  · exact u35704
  · exact u35705

def r42532 : Route 9 := (fun mask => (mask,id))

def c42532 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42532 : Upper (D 6) (R 6) [34,65,136,17] 13 := by
  apply FastRouting.sound _ _ [34,65,136,17] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r42532 c42532
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35706
  · exact u35707
  · exact u35708
  · exact u35709
  · exact u35710
  · exact u35711
  · exact u35712
  · exact u35713
  · exact u35714
  · exact u35715

theorem m42533_6 : Upper (D 6) (R 6) [34,65,136,20,6] 13 :=
  permutation_upper _ _ _ [34,65,136,20,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35717

theorem m42533_65 : Upper (D 6) (R 6) [34,65,136,20,65] 13 :=
  permutation_upper _ _ _ [34,65,136,20,34] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35719

theorem m42533_66 : Upper (D 6) (R 6) [34,65,136,20,66] 13 :=
  permutation_upper _ _ _ [34,65,136,20,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35718

theorem m42533_68 : Upper (D 6) (R 6) [34,65,136,20,68] 13 :=
  permutation_upper _ _ _ [34,65,136,20,36] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35720

theorem m42533_258 : Upper (D 6) (R 6) [34,65,136,20,258] 13 :=
  permutation_upper _ _ _ [34,65,136,20,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35722

theorem m42533_320 : Upper (D 6) (R 6) [34,65,136,20,320] 13 :=
  permutation_upper _ _ _ [34,65,136,20,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35724

def r42533 : Route 9 := (fun mask => (mask,id))

def c42533 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42533 : Upper (D 6) (R 6) [34,65,136,20] 13 := by
  apply FastRouting.sound _ _ [34,65,136,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r42533 c42533
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35716
  · exact u35717
  · exact m42533_6
  · exact u35718
  · exact u35719
  · exact u35720
  · exact m42533_65
  · exact m42533_66
  · exact m42533_68
  · exact u35721
  · exact u35722
  · exact m42533_258
  · exact u35723
  · exact u35724
  · exact m42533_320

def b42534 : PairBound 9 := { available := 342, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 67 140 41 342 374 342 470 342), lower := (rows 35 67 140 41 16 32 64 128 256), losses := [] }

theorem u42534 : Upper (D 6) (R 6) [34,65,136,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b42535 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 67 140 42 341 373 341 469 341), lower := (rows 35 67 140 42 16 32 64 128 256), losses := [] }

theorem u42535 : Upper (D 6) (R 6) [34,65,136,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b42535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r42536 : Route 9 := (fun mask => (mask,id))

def c42536 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42536 : Upper (D 6) (R 6) [34,65,136,36] 13 := by
  apply FastRouting.sound _ _ [34,65,136,36] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42536 c42536
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35725
  · exact u35726
  · exact u35727
  · exact u35728
  · exact u35729
  · exact u35730
  · exact u35731
  · exact u35732
  · exact u35733
  · exact u35734

def r42537 : Route 9 := (fun mask => (mask,id))

def c42537 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u42537 : Upper (D 6) (R 6) [34,65,136,48] 13 := by
  apply FastRouting.sound _ _ [34,65,136,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r42537 c42537
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35735
  · exact u35736
  · exact u35737
  · exact u35738
  · exact u35739
  · exact u35740
  · exact u35741
  · exact u35742
  · exact u35743
  · exact u35744

theorem m42538_6 : Upper (D 6) (R 6) [34,65,136,96,6] 13 :=
  permutation_upper _ _ _ [34,65,136,96,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35746

theorem m42538_258 : Upper (D 6) (R 6) [34,65,136,96,258] 13 :=
  permutation_upper _ _ _ [34,65,136,96,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u35747

def r42538 : Route 9 := (fun mask => (mask,id))

def c42538 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 3 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u42538 : Upper (D 6) (R 6) [34,65,136,96] 13 := by
  apply FastRouting.sound _ _ [34,65,136,96] 13 (by decide) (choices 2) [3,5,6,257,258,260] r42538 c42538
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35745
  · exact u35746
  · exact m42538_6
  · exact u35747
  · exact m42538_258
  · exact u35748

def r42539 : Route 9 := (fun mask => (mask,id))

def c42539 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u42539 : Upper (D 6) (R 6) [34,65,136,257] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r42539 c42539
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u35749
  · exact u35750
  · exact u35751
  · exact u35752
  · exact u35753
  · exact u35754

#print axioms u42539
end Delivery.IrregularNine14.P06
