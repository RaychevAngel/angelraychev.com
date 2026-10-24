import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0056
import IrregularNine14P03C0057
import IrregularNine14P03C0058
import IrregularNine14P03C0059

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m6240_9 : Upper (D 3) (R 3) [34,68,129,192,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3380

theorem m6240_33 : Upper (D 3) (R 3) [34,68,129,192,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3388

theorem m6240_40 : Upper (D 3) (R 3) [34,68,129,192,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3397

def r6240 : Route 9 := (fun mask => (mask,id))

def c6240 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u6240 : Upper (D 3) (R 3) [34,68,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r6240 c6240
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6240_9
  · exact m6240_33
  · exact m6240_40
  · exact u3431
  · exact u3432
  · exact u3433

theorem m6241_9 : Upper (D 3) (R 3) [34,68,129,257,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3381

theorem m6241_33 : Upper (D 3) (R 3) [34,68,129,257,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3389

theorem m6241_40 : Upper (D 3) (R 3) [34,68,129,257,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3398

theorem m6241_65 : Upper (D 3) (R 3) [34,68,129,257,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3404

theorem m6241_72 : Upper (D 3) (R 3) [34,68,129,257,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3411

theorem m6241_96 : Upper (D 3) (R 3) [34,68,129,257,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3417

theorem m6241_129 : Upper (D 3) (R 3) [34,68,129,257,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3420

theorem m6241_136 : Upper (D 3) (R 3) [34,68,129,257,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3424

theorem m6241_160 : Upper (D 3) (R 3) [34,68,129,257,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3428

theorem m6241_192 : Upper (D 3) (R 3) [34,68,129,257,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3431

def r6241 : Route 9 := (fun mask => (mask,id))

def c6241 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6241 : Upper (D 3) (R 3) [34,68,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6241 c6241
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6241_9
  · exact m6241_33
  · exact m6241_40
  · exact m6241_65
  · exact m6241_72
  · exact m6241_96
  · exact m6241_129
  · exact m6241_136
  · exact m6241_160
  · exact m6241_192

theorem m6242_9 : Upper (D 3) (R 3) [34,68,129,272,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3382

theorem m6242_33 : Upper (D 3) (R 3) [34,68,129,272,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3390

theorem m6242_40 : Upper (D 3) (R 3) [34,68,129,272,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3399

theorem m6242_65 : Upper (D 3) (R 3) [34,68,129,272,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3405

theorem m6242_72 : Upper (D 3) (R 3) [34,68,129,272,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3412

theorem m6242_96 : Upper (D 3) (R 3) [34,68,129,272,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3418

theorem m6242_129 : Upper (D 3) (R 3) [34,68,129,272,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3421

theorem m6242_136 : Upper (D 3) (R 3) [34,68,129,272,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3425

theorem m6242_160 : Upper (D 3) (R 3) [34,68,129,272,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3429

theorem m6242_192 : Upper (D 3) (R 3) [34,68,129,272,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3432

def r6242 : Route 9 := (fun mask => (mask,id))

def c6242 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6242 : Upper (D 3) (R 3) [34,68,129,272] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6242 c6242
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6242_9
  · exact m6242_33
  · exact m6242_40
  · exact m6242_65
  · exact m6242_72
  · exact m6242_96
  · exact m6242_129
  · exact m6242_136
  · exact m6242_160
  · exact m6242_192

theorem m6243_9 : Upper (D 3) (R 3) [34,68,129,288,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3383

theorem m6243_65 : Upper (D 3) (R 3) [34,68,129,288,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3406

theorem m6243_72 : Upper (D 3) (R 3) [34,68,129,288,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3413

theorem m6243_129 : Upper (D 3) (R 3) [34,68,129,288,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3422

theorem m6243_136 : Upper (D 3) (R 3) [34,68,129,288,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3426

theorem m6243_192 : Upper (D 3) (R 3) [34,68,129,288,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3433

def r6243 : Route 9 := (fun mask => (mask,id))

def c6243 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6243 : Upper (D 3) (R 3) [34,68,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,288] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6243 c6243
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6243_9
  · exact m6243_65
  · exact m6243_72
  · exact m6243_129
  · exact m6243_136
  · exact m6243_192

theorem m6244_9 : Upper (D 3) (R 3) [34,68,129,320,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3384

theorem m6244_33 : Upper (D 3) (R 3) [34,68,129,320,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3391

theorem m6244_40 : Upper (D 3) (R 3) [34,68,129,320,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3400

theorem m6244_129 : Upper (D 3) (R 3) [34,68,129,320,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3423

theorem m6244_136 : Upper (D 3) (R 3) [34,68,129,320,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3427

theorem m6244_160 : Upper (D 3) (R 3) [34,68,129,320,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3430

def r6244 : Route 9 := (fun mask => (mask,id))

def c6244 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6244 : Upper (D 3) (R 3) [34,68,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6244 c6244
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6244_9
  · exact m6244_33
  · exact m6244_40
  · exact m6244_129
  · exact m6244_136
  · exact m6244_160

theorem m6245_9 : Upper (D 3) (R 3) [34,68,129,384,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3385

theorem m6245_33 : Upper (D 3) (R 3) [34,68,129,384,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3392

theorem m6245_40 : Upper (D 3) (R 3) [34,68,129,384,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3401

theorem m6245_65 : Upper (D 3) (R 3) [34,68,129,384,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3407

theorem m6245_72 : Upper (D 3) (R 3) [34,68,129,384,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3414

theorem m6245_96 : Upper (D 3) (R 3) [34,68,129,384,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3419

def r6245 : Route 9 := (fun mask => (mask,id))

def c6245 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u6245 : Upper (D 3) (R 3) [34,68,129,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,384] 13 (by decide) (choices 2) [9,33,40,65,72,96] r6245 c6245
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6245_9
  · exact m6245_33
  · exact m6245_40
  · exact m6245_65
  · exact m6245_72
  · exact m6245_96

def r6246 : Route 9 := (fun mask => (mask,id))

def c6246 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6246 : Upper (D 3) (R 3) [34,68,136,17] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r6246 c6246
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3434
  · exact u3435
  · exact u3436
  · exact u3437
  · exact u3438
  · exact u3439
  · exact u3440
  · exact u3441
  · exact u3442
  · exact u3443

def b6247 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 140 41 465 497 465 465 465), lower := (rows 35 70 140 41 16 32 64 128 256), losses := [] }

theorem u6247 : Upper (D 3) (R 3) [34,68,136,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6247
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6248 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 140 56 465 481 449 449 449), lower := (rows 35 70 140 56 16 32 64 128 256), losses := [] }

theorem u6248 : Upper (D 3) (R 3) [34,68,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6248
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6249 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 73 433 433 497 433 433), lower := (rows 35 70 140 73 16 32 64 128 256), losses := [] }

theorem u6249 : Upper (D 3) (R 3) [34,68,136,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6249
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6250 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 88 433 417 481 417 417), lower := (rows 35 70 140 88 16 32 64 128 256), losses := [] }

theorem u6250 : Upper (D 3) (R 3) [34,68,136,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6250
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6251 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 104 401 433 465 401 401), lower := (rows 35 70 140 104 16 32 64 128 256), losses := [] }

theorem u6251 : Upper (D 3) (R 3) [34,68,136,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6251
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6252 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 137 369 369 369 497 369), lower := (rows 35 70 140 137 16 32 64 128 256), losses := [] }

theorem u6252 : Upper (D 3) (R 3) [34,68,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6252
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6253 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 152 369 353 353 481 353), lower := (rows 35 70 140 152 16 32 64 128 256), losses := [] }

theorem u6253 : Upper (D 3) (R 3) [34,68,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6253
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6254 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 168 337 369 337 465 337), lower := (rows 35 70 140 168 16 32 64 128 256), losses := [] }

theorem u6254 : Upper (D 3) (R 3) [34,68,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6254
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6255 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 140 200 305 305 369 433 305), lower := (rows 35 70 140 200 16 32 64 128 256), losses := [] }

theorem u6255 : Upper (D 3) (R 3) [34,68,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6255
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6256 : Route 9 := (fun mask => (mask,id))

def c6256 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6256 : Upper (D 3) (R 3) [34,68,136,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6256 c6256
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3444
  · exact u3445
  · exact u3446
  · exact u3447
  · exact u3448
  · exact u3449

def r6257 : Route 9 := (fun mask => (mask,id))

def c6257 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6257 : Upper (D 3) (R 3) [34,68,136,272] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6257 c6257
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3450
  · exact u3451
  · exact u3452
  · exact u3453
  · exact u3454
  · exact u3455

def b6258 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 140 296 209 241 209 209 465), lower := (rows 35 70 140 296 16 32 64 128 256), losses := [] }

theorem u6258 : Upper (D 3) (R 3) [34,68,136,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6258
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6259 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 328 177 177 241 177 433), lower := (rows 35 70 140 328 16 32 64 128 256), losses := [] }

theorem u6259 : Upper (D 3) (R 3) [34,68,136,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6259
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6260 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 392 113 113 113 241 369), lower := (rows 35 70 140 392 16 32 64 128 256), losses := [] }

theorem u6260 : Upper (D 3) (R 3) [34,68,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6260
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6261 : Route 9 := (fun mask => (mask,id))

def c6261 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6261 : Upper (D 3) (R 3) [34,68,257,17] 13 := by
  apply FastRouting.sound _ _ [34,68,257,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6261 c6261
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3456
  · exact u3457
  · exact u3458
  · exact u3459
  · exact u3460
  · exact u3461
  · exact u3462
  · exact u3463
  · exact u3464
  · exact u3465

def b6262 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 261 41 217 249 217 217 473), lower := (rows 35 70 261 41 16 32 64 128 256), losses := [] }

theorem u6262 : Upper (D 3) (R 3) [34,68,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6262
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6263_9 : Upper (D 3) (R 3) [34,68,257,48,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3458

def r6263 : Route 9 := (fun mask => (mask,id))

def c6263 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6263 : Upper (D 3) (R 3) [34,68,257,48] 13 := by
  apply FastRouting.sound _ _ [34,68,257,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6263 c6263
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6263_9
  · exact u3470
  · exact u3471
  · exact u3472
  · exact u3473
  · exact u3474

def b6264 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 73 185 185 249 185 441), lower := (rows 35 70 261 73 16 32 64 128 256), losses := [] }

theorem u6264 : Upper (D 3) (R 3) [34,68,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6264
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6265_9 : Upper (D 3) (R 3) [34,68,257,80,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3460

theorem m6265_33 : Upper (D 3) (R 3) [34,68,257,80,33] 13 :=
  permutation_upper _ _ _ [34,68,257,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3466

theorem m6265_40 : Upper (D 3) (R 3) [34,68,257,80,40] 13 :=
  permutation_upper _ _ _ [34,68,257,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3471

def r6265 : Route 9 := (fun mask => (mask,id))

def c6265 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6265 : Upper (D 3) (R 3) [34,68,257,80] 13 := by
  apply FastRouting.sound _ _ [34,68,257,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6265 c6265
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6265_9
  · exact m6265_33
  · exact m6265_40
  · exact u3478
  · exact u3479
  · exact u3480

theorem m6266_9 : Upper (D 3) (R 3) [34,68,257,96,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3461

def r6266 : Route 9 := (fun mask => (mask,id))

def c6266 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6266 : Upper (D 3) (R 3) [34,68,257,96] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96] 13 (by decide) (choices 2) [9,129,136] r6266 c6266
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6266_9
  · exact u3481
  · exact u3482

theorem m6267_9 : Upper (D 3) (R 3) [34,68,257,129,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3462

theorem m6267_33 : Upper (D 3) (R 3) [34,68,257,129,33] 13 :=
  permutation_upper _ _ _ [34,68,257,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3467

theorem m6267_40 : Upper (D 3) (R 3) [34,68,257,129,40] 13 :=
  permutation_upper _ _ _ [34,68,257,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3472

theorem m6267_65 : Upper (D 3) (R 3) [34,68,257,129,65] 13 :=
  permutation_upper _ _ _ [34,68,257,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3475

theorem m6267_72 : Upper (D 3) (R 3) [34,68,257,129,72] 13 :=
  permutation_upper _ _ _ [34,68,257,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3478

theorem m6267_96 : Upper (D 3) (R 3) [34,68,257,129,96] 13 :=
  permutation_upper _ _ _ [34,68,257,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3481

def r6267 : Route 9 := (fun mask => (mask,id))

def c6267 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6267 : Upper (D 3) (R 3) [34,68,257,129] 13 := by
  apply FastRouting.sound _ _ [34,68,257,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6267 c6267
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6267_9
  · exact m6267_33
  · exact m6267_40
  · exact m6267_65
  · exact m6267_72
  · exact m6267_96
  · exact u3483
  · exact u3484
  · exact u3485
  · exact u3486

theorem m6268_9 : Upper (D 3) (R 3) [34,68,257,144,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3463

theorem m6268_33 : Upper (D 3) (R 3) [34,68,257,144,33] 13 :=
  permutation_upper _ _ _ [34,68,257,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3468

theorem m6268_40 : Upper (D 3) (R 3) [34,68,257,144,40] 13 :=
  permutation_upper _ _ _ [34,68,257,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3473

theorem m6268_65 : Upper (D 3) (R 3) [34,68,257,144,65] 13 :=
  permutation_upper _ _ _ [34,68,257,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3476

theorem m6268_72 : Upper (D 3) (R 3) [34,68,257,144,72] 13 :=
  permutation_upper _ _ _ [34,68,257,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3479

theorem m6268_96 : Upper (D 3) (R 3) [34,68,257,144,96] 13 :=
  permutation_upper _ _ _ [34,68,257,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3482

theorem m6268_129 : Upper (D 3) (R 3) [34,68,257,144,129] 13 :=
  permutation_upper _ _ _ [34,68,257,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3484

def r6268 : Route 9 := (fun mask => (mask,id))

def c6268 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6268 : Upper (D 3) (R 3) [34,68,257,144] 13 := by
  apply FastRouting.sound _ _ [34,68,257,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6268 c6268
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6268_9
  · exact m6268_33
  · exact m6268_40
  · exact m6268_65
  · exact m6268_72
  · exact m6268_96
  · exact m6268_129
  · exact u3487
  · exact u3488
  · exact u3489

theorem m6269_9 : Upper (D 3) (R 3) [34,68,257,160,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3464

theorem m6269_65 : Upper (D 3) (R 3) [34,68,257,160,65] 13 :=
  permutation_upper _ _ _ [34,68,257,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3477

theorem m6269_72 : Upper (D 3) (R 3) [34,68,257,160,72] 13 :=
  permutation_upper _ _ _ [34,68,257,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3480

theorem m6269_129 : Upper (D 3) (R 3) [34,68,257,160,129] 13 :=
  permutation_upper _ _ _ [34,68,257,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3485

theorem m6269_136 : Upper (D 3) (R 3) [34,68,257,160,136] 13 :=
  permutation_upper _ _ _ [34,68,257,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3488

def r6269 : Route 9 := (fun mask => (mask,id))

def c6269 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6269 : Upper (D 3) (R 3) [34,68,257,160] 13 := by
  apply FastRouting.sound _ _ [34,68,257,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6269 c6269
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6269_9
  · exact m6269_65
  · exact m6269_72
  · exact m6269_129
  · exact m6269_136
  · exact u3490

theorem m6270_9 : Upper (D 3) (R 3) [34,68,257,192,9] 13 :=
  permutation_upper _ _ _ [34,68,257,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3465

theorem m6270_33 : Upper (D 3) (R 3) [34,68,257,192,33] 13 :=
  permutation_upper _ _ _ [34,68,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3469

theorem m6270_40 : Upper (D 3) (R 3) [34,68,257,192,40] 13 :=
  permutation_upper _ _ _ [34,68,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3474

theorem m6270_129 : Upper (D 3) (R 3) [34,68,257,192,129] 13 :=
  permutation_upper _ _ _ [34,68,257,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3486

theorem m6270_136 : Upper (D 3) (R 3) [34,68,257,192,136] 13 :=
  permutation_upper _ _ _ [34,68,257,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3489

theorem m6270_160 : Upper (D 3) (R 3) [34,68,257,192,160] 13 :=
  permutation_upper _ _ _ [34,68,257,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3490

def r6270 : Route 9 := (fun mask => (mask,id))

def c6270 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6270 : Upper (D 3) (R 3) [34,68,257,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6270 c6270
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6270_9
  · exact m6270_33
  · exact m6270_40
  · exact m6270_129
  · exact m6270_136
  · exact m6270_160

def r6271 : Route 9 := (fun mask => (mask,id))

def c6271 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6271 : Upper (D 3) (R 3) [34,68,264,17] 13 := by
  apply FastRouting.sound _ _ [34,68,264,17] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6271 c6271
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3491
  · exact u3492
  · exact u3493
  · exact u3494
  · exact u3495
  · exact u3496

def b6272 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 268 41 209 241 209 209 465), lower := (rows 35 70 268 41 16 32 64 128 256), losses := [] }

theorem u6272 : Upper (D 3) (R 3) [34,68,264,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6272
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6273 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 268 56 209 225 193 193 449), lower := (rows 35 70 268 56 16 32 64 128 256), losses := [] }

theorem u6273 : Upper (D 3) (R 3) [34,68,264,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6273
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6274 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 73 177 177 241 177 433), lower := (rows 35 70 268 73 16 32 64 128 256), losses := [] }

theorem u6274 : Upper (D 3) (R 3) [34,68,264,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6274
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6275 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 88 177 161 225 161 417), lower := (rows 35 70 268 88 16 32 64 128 256), losses := [] }

theorem u6275 : Upper (D 3) (R 3) [34,68,264,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6275
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6276 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 104 145 177 209 145 401), lower := (rows 35 70 268 104 16 32 64 128 256), losses := [] }

theorem u6276 : Upper (D 3) (R 3) [34,68,264,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6276
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6277 : Route 9 := (fun mask => (mask,id))

def c6277 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6277 : Upper (D 3) (R 3) [34,68,264,129] 13 := by
  apply FastRouting.sound _ _ [34,68,264,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6277 c6277
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3497
  · exact u3498
  · exact u3499
  · exact u3500
  · exact u3501
  · exact u3502

def r6278 : Route 9 := (fun mask => (mask,id))

def c6278 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6278 : Upper (D 3) (R 3) [34,68,264,144] 13 := by
  apply FastRouting.sound _ _ [34,68,264,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6278 c6278
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3503
  · exact u3504
  · exact u3505
  · exact u3506
  · exact u3507
  · exact u3508

def b6279 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 268 168 209 241 209 209 465), lower := (rows 35 70 268 168 16 32 64 128 256), losses := [] }

theorem u6279 : Upper (D 3) (R 3) [34,68,264,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6279
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6280 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 200 177 177 241 177 433), lower := (rows 35 70 268 200 16 32 64 128 256), losses := [] }

theorem u6280 : Upper (D 3) (R 3) [34,68,264,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6280
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6281 : Route 9 := (fun mask => (mask,id))

def c6281 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6281 : Upper (D 3) (R 3) [34,68,384,17] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6281 c6281
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3509
  · exact u3510
  · exact u3511
  · exact u3512
  · exact u3513
  · exact u3514
  · exact u3515
  · exact u3516
  · exact u3517
  · exact u3518

def b6282 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 388 41 217 249 217 217 473), lower := (rows 35 70 388 41 16 32 64 128 256), losses := [] }

theorem u6282 : Upper (D 3) (R 3) [34,68,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6282
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6283_9 : Upper (D 3) (R 3) [34,68,384,48,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3511

def r6283 : Route 9 := (fun mask => (mask,id))

def c6283 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6283 : Upper (D 3) (R 3) [34,68,384,48] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6283 c6283
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6283_9
  · exact u3522
  · exact u3523
  · exact u3524
  · exact u3525
  · exact u3526

def b6284 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 73 185 185 249 185 441), lower := (rows 35 70 388 73 16 32 64 128 256), losses := [] }

theorem u6284 : Upper (D 3) (R 3) [34,68,384,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6284
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6285_9 : Upper (D 3) (R 3) [34,68,384,80,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3513

theorem m6285_33 : Upper (D 3) (R 3) [34,68,384,80,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3519

theorem m6285_40 : Upper (D 3) (R 3) [34,68,384,80,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3523

def r6285 : Route 9 := (fun mask => (mask,id))

def c6285 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6285 : Upper (D 3) (R 3) [34,68,384,80] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6285 c6285
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6285_9
  · exact m6285_33
  · exact m6285_40
  · exact u3529
  · exact u3530
  · exact u3531

theorem m6286_9 : Upper (D 3) (R 3) [34,68,384,96,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3514

def r6286 : Route 9 := (fun mask => (mask,id))

def c6286 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6286 : Upper (D 3) (R 3) [34,68,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96] 13 (by decide) (choices 2) [9,129,136] r6286 c6286
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6286_9
  · exact u3532
  · exact u3533

def b6287 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 388 137 121 121 121 249 377), lower := (rows 35 70 388 137 16 32 64 128 256), losses := [] }

theorem u6287 : Upper (D 3) (R 3) [34,68,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6287
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6288_9 : Upper (D 3) (R 3) [34,68,384,144,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3516

theorem m6288_33 : Upper (D 3) (R 3) [34,68,384,144,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3520

theorem m6288_40 : Upper (D 3) (R 3) [34,68,384,144,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3525

theorem m6288_65 : Upper (D 3) (R 3) [34,68,384,144,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3527

theorem m6288_72 : Upper (D 3) (R 3) [34,68,384,144,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3530

theorem m6288_96 : Upper (D 3) (R 3) [34,68,384,144,96] 13 :=
  permutation_upper _ _ _ [34,68,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3533

def r6288 : Route 9 := (fun mask => (mask,id))

def c6288 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u6288 : Upper (D 3) (R 3) [34,68,384,144] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144] 13 (by decide) (choices 2) [9,33,40,65,72,96] r6288 c6288
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6288_9
  · exact m6288_33
  · exact m6288_40
  · exact m6288_65
  · exact m6288_72
  · exact m6288_96

theorem m6289_9 : Upper (D 3) (R 3) [34,68,384,160,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3517

theorem m6289_65 : Upper (D 3) (R 3) [34,68,384,160,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3528

theorem m6289_72 : Upper (D 3) (R 3) [34,68,384,160,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3531

def r6289 : Route 9 := (fun mask => (mask,id))

def c6289 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u6289 : Upper (D 3) (R 3) [34,68,384,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,160] 13 (by decide) (choices 2) [9,65,72] r6289 c6289
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6289_9
  · exact m6289_65
  · exact m6289_72

theorem m6290_9 : Upper (D 3) (R 3) [34,68,384,192,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3518

theorem m6290_33 : Upper (D 3) (R 3) [34,68,384,192,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3521

theorem m6290_40 : Upper (D 3) (R 3) [34,68,384,192,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3526

def r6290 : Route 9 := (fun mask => (mask,id))

def c6290 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u6290 : Upper (D 3) (R 3) [34,68,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,192] 13 (by decide) (choices 2) [9,33,40] r6290 c6290
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m6290_9
  · exact m6290_33
  · exact m6290_40

def b6291 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 13 497 497 497 497 497), lower := (rows 35 194 13 13 16 32 64 128 256), losses := [] }

theorem u6291 : Upper (D 3) (R 3) [34,192,9,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6291
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6292 : PairBound 9 := { available := 485, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 25 501 485 485 485 485), lower := (rows 35 194 13 25 16 32 64 128 256), losses := [] }

theorem u6292 : Upper (D 3) (R 3) [34,192,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6292
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6293 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6293 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6293 : Upper (D 3) (R 3) [34,192,9,20] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r6293 c6293
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3545
  · exact u3546
  · exact u3547
  · exact u3548
  · exact u3549
  · exact u3550
  · exact u3551

def b6294 : PairBound 9 := { available := 469, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 41 469 501 469 469 469), lower := (rows 35 194 13 41 16 32 64 128 256), losses := [] }

theorem u6294 : Upper (D 3) (R 3) [34,192,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6294
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6295 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 44 465 497 465 465 465), lower := (rows 35 194 13 44 16 32 64 128 256), losses := [] }

theorem u6295 : Upper (D 3) (R 3) [34,192,9,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6295
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6296 : PairBound 9 := { available := 453, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 194 13 56 469 485 453 453 453), lower := (rows 35 194 13 56 16 32 64 128 256), losses := [] }

theorem u6296 : Upper (D 3) (R 3) [34,192,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6296
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6297 : PairBound 9 := { available := 437, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 13 73 437 437 501 437 437), lower := (rows 35 194 13 73 16 32 64 128 256), losses := [] }

theorem u6297 : Upper (D 3) (R 3) [34,192,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6297
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6298 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 76 433 433 497 433 433), lower := (rows 35 194 13 76 16 32 64 128 256), losses := [] }

theorem u6298 : Upper (D 3) (R 3) [34,192,9,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6298
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6299 : PairBound 9 := { available := 421, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 194 13 88 437 421 485 421 421), lower := (rows 35 194 13 88 16 32 64 128 256), losses := [] }

theorem u6299 : Upper (D 3) (R 3) [34,192,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6299
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u6299
end Delivery.IrregularNine14.P03
