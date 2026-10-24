import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0127
import IrregularNine14P08C0128
import IrregularNine14P08C0129
import IrregularNine14P08C0130

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m19020_9 : Upper (D 8) (R 8) [6,65,160,192,9] 13 :=
  permutation_upper _ _ _ [6,65,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7631

theorem m19020_33 : Upper (D 8) (R 8) [6,65,160,192,33] 13 :=
  permutation_upper _ _ _ [6,65,160,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7640

theorem m19020_40 : Upper (D 8) (R 8) [6,65,160,192,40] 13 :=
  permutation_upper _ _ _ [6,65,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7652

def r19020 : Route 9 := (fun mask => (mask,id))

def c19020 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u19020 : Upper (D 8) (R 8) [6,65,160,192] 13 := by
  apply FastRouting.sound _ _ [6,65,160,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r19020 c19020
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19020_9
  · exact m19020_33
  · exact m19020_40
  · exact u7686
  · exact u7687
  · exact u7688

def b19021 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 265 248 248 248 248 504), lower := (rows 7 67 164 265 16 32 64 128 256), losses := [] }

theorem u19021 : Upper (D 8) (R 8) [6,65,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19021 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19022_9 : Upper (D 8) (R 8) [6,65,160,272,9] 13 :=
  permutation_upper _ _ _ [6,65,160,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7632

theorem m19022_33 : Upper (D 8) (R 8) [6,65,160,272,33] 13 :=
  permutation_upper _ _ _ [6,65,160,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7641

theorem m19022_40 : Upper (D 8) (R 8) [6,65,160,272,40] 13 :=
  permutation_upper _ _ _ [6,65,160,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7654

theorem m19022_65 : Upper (D 8) (R 8) [6,65,160,272,65] 13 :=
  permutation_upper _ _ _ [6,65,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7659

theorem m19022_72 : Upper (D 8) (R 8) [6,65,160,272,72] 13 :=
  permutation_upper _ _ _ [6,65,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7666

theorem m19022_96 : Upper (D 8) (R 8) [6,65,160,272,96] 13 :=
  permutation_upper _ _ _ [6,65,160,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7673

theorem m19022_129 : Upper (D 8) (R 8) [6,65,160,272,129] 13 :=
  permutation_upper _ _ _ [6,65,160,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7676

theorem m19022_136 : Upper (D 8) (R 8) [6,65,160,272,136] 13 :=
  permutation_upper _ _ _ [6,65,160,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7680

theorem m19022_160 : Upper (D 8) (R 8) [6,65,160,272,160] 13 :=
  permutation_upper _ _ _ [6,65,160,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7683

theorem m19022_192 : Upper (D 8) (R 8) [6,65,160,272,192] 13 :=
  permutation_upper _ _ _ [6,65,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7687

def r19022 : Route 9 := (fun mask => (mask,id))

def c19022 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19022 : Upper (D 8) (R 8) [6,65,160,272] 13 := by
  apply FastRouting.sound _ _ [6,65,160,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19022 c19022
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19022_9
  · exact m19022_33
  · exact m19022_40
  · exact m19022_65
  · exact m19022_72
  · exact m19022_96
  · exact m19022_129
  · exact m19022_136
  · exact m19022_160
  · exact m19022_192

theorem m19023_9 : Upper (D 8) (R 8) [6,65,160,288,9] 13 :=
  permutation_upper _ _ _ [6,65,160,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7633

theorem m19023_33 : Upper (D 8) (R 8) [6,65,160,288,33] 13 :=
  permutation_upper _ _ _ [6,65,160,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7642

theorem m19023_40 : Upper (D 8) (R 8) [6,65,160,288,40] 13 :=
  permutation_upper _ _ _ [6,65,160,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7655

theorem m19023_65 : Upper (D 8) (R 8) [6,65,160,288,65] 13 :=
  permutation_upper _ _ _ [6,65,160,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7660

theorem m19023_72 : Upper (D 8) (R 8) [6,65,160,288,72] 13 :=
  permutation_upper _ _ _ [6,65,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7667

theorem m19023_96 : Upper (D 8) (R 8) [6,65,160,288,96] 13 :=
  permutation_upper _ _ _ [6,65,160,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7674

theorem m19023_129 : Upper (D 8) (R 8) [6,65,160,288,129] 13 :=
  permutation_upper _ _ _ [6,65,160,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7677

theorem m19023_136 : Upper (D 8) (R 8) [6,65,160,288,136] 13 :=
  permutation_upper _ _ _ [6,65,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7681

theorem m19023_160 : Upper (D 8) (R 8) [6,65,160,288,160] 13 :=
  permutation_upper _ _ _ [6,65,160,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7684

theorem m19023_192 : Upper (D 8) (R 8) [6,65,160,288,192] 13 :=
  permutation_upper _ _ _ [6,65,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7688

def r19023 : Route 9 := (fun mask => (mask,id))

def c19023 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19023 : Upper (D 8) (R 8) [6,65,160,288] 13 := by
  apply FastRouting.sound _ _ [6,65,160,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19023 c19023
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19023_9
  · exact m19023_33
  · exact m19023_40
  · exact m19023_65
  · exact m19023_72
  · exact m19023_96
  · exact m19023_129
  · exact m19023_136
  · exact m19023_160
  · exact m19023_192

theorem m19024_9 : Upper (D 8) (R 8) [6,65,160,320,9] 13 :=
  permutation_upper _ _ _ [6,65,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7634

theorem m19024_33 : Upper (D 8) (R 8) [6,65,160,320,33] 13 :=
  permutation_upper _ _ _ [6,65,160,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7643

theorem m19024_40 : Upper (D 8) (R 8) [6,65,160,320,40] 13 :=
  permutation_upper _ _ _ [6,65,160,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7656

theorem m19024_129 : Upper (D 8) (R 8) [6,65,160,320,129] 13 :=
  permutation_upper _ _ _ [6,65,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7678

theorem m19024_136 : Upper (D 8) (R 8) [6,65,160,320,136] 13 :=
  permutation_upper _ _ _ [6,65,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7682

theorem m19024_160 : Upper (D 8) (R 8) [6,65,160,320,160] 13 :=
  permutation_upper _ _ _ [6,65,160,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7685

def r19024 : Route 9 := (fun mask => (mask,id))

def c19024 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19024 : Upper (D 8) (R 8) [6,65,160,320] 13 := by
  apply FastRouting.sound _ _ [6,65,160,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19024 c19024
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19024_9
  · exact m19024_33
  · exact m19024_40
  · exact m19024_129
  · exact m19024_136
  · exact m19024_160

theorem m19025_9 : Upper (D 8) (R 8) [6,65,160,384,9] 13 :=
  permutation_upper _ _ _ [6,65,160,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7635

theorem m19025_33 : Upper (D 8) (R 8) [6,65,160,384,33] 13 :=
  permutation_upper _ _ _ [6,65,160,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7644

theorem m19025_40 : Upper (D 8) (R 8) [6,65,160,384,40] 13 :=
  permutation_upper _ _ _ [6,65,160,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7657

theorem m19025_65 : Upper (D 8) (R 8) [6,65,160,384,65] 13 :=
  permutation_upper _ _ _ [6,65,160,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7661

theorem m19025_72 : Upper (D 8) (R 8) [6,65,160,384,72] 13 :=
  permutation_upper _ _ _ [6,65,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7668

theorem m19025_96 : Upper (D 8) (R 8) [6,65,160,384,96] 13 :=
  permutation_upper _ _ _ [6,65,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7675

def r19025 : Route 9 := (fun mask => (mask,id))

def c19025 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19025 : Upper (D 8) (R 8) [6,65,160,384] 13 := by
  apply FastRouting.sound _ _ [6,65,160,384] 13 (by decide) (choices 2) [9,33,40,65,72,96] r19025 c19025
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19025_9
  · exact m19025_33
  · exact m19025_40
  · exact m19025_65
  · exact m19025_72
  · exact m19025_96

def b19026 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 268 25 240 224 224 224 480), lower := (rows 7 67 268 25 16 32 64 128 256), losses := [] }

theorem u19026 : Upper (D 8) (R 8) [6,65,264,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19027 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 268 41 240 240 240 240 496), lower := (rows 7 67 268 41 16 32 64 128 256), losses := [] }

theorem u19027 : Upper (D 8) (R 8) [6,65,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19028 : Route 9 := (fun mask => (mask,id))

def c19028 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19028 : Upper (D 8) (R 8) [6,65,264,48] 13 := by
  apply FastRouting.sound _ _ [6,65,264,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19028 c19028
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7689
  · exact u7690
  · exact u7691
  · exact u7692
  · exact u7693
  · exact u7694

def b19029 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 268 73 176 176 240 176 432), lower := (rows 7 67 268 73 16 32 64 128 256), losses := [] }

theorem u19029 : Upper (D 8) (R 8) [6,65,264,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19029 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19030 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 67 268 88 177 161 225 161 417), lower := (rows 7 67 268 88 16 32 64 128 256), losses := [] }

theorem u19030 : Upper (D 8) (R 8) [6,65,264,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19031 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 67 268 104 177 177 241 177 433), lower := (rows 7 67 268 104 16 32 64 128 256), losses := [] }

theorem u19031 : Upper (D 8) (R 8) [6,65,264,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19032 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 268 137 240 240 240 240 496), lower := (rows 7 67 268 137 16 32 64 128 256), losses := [] }

theorem u19032 : Upper (D 8) (R 8) [6,65,264,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19033 : Route 9 := (fun mask => (mask,id))

def c19033 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19033 : Upper (D 8) (R 8) [6,65,264,144] 13 := by
  apply FastRouting.sound _ _ [6,65,264,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19033 c19033
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7695
  · exact u7696
  · exact u7697
  · exact u7698
  · exact u7699
  · exact u7700

def r19034 : Route 9 := (fun mask => (mask,id))

def c19034 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19034 : Upper (D 8) (R 8) [6,65,264,160] 13 := by
  apply FastRouting.sound _ _ [6,65,264,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19034 c19034
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7701
  · exact u7702
  · exact u7703
  · exact u7704
  · exact u7705
  · exact u7706

def b19035 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 67 268 200 177 177 241 177 433), lower := (rows 7 67 268 200 16 32 64 128 256), losses := [] }

theorem u19035 : Upper (D 8) (R 8) [6,65,264,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19036 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 25 248 232 232 232 488), lower := (rows 7 67 292 25 16 32 64 128 256), losses := [] }

theorem u19036 : Upper (D 8) (R 8) [6,65,288,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19037 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 41 248 248 248 248 504), lower := (rows 7 67 292 41 16 32 64 128 256), losses := [] }

theorem u19037 : Upper (D 8) (R 8) [6,65,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19038_9 : Upper (D 8) (R 8) [6,65,288,48,9] 13 :=
  permutation_upper _ _ _ [6,65,288,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7707

theorem m19038_33 : Upper (D 8) (R 8) [6,65,288,48,33] 13 :=
  permutation_upper _ _ _ [6,65,288,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7713

def r19038 : Route 9 := (fun mask => (mask,id))

def c19038 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19038 : Upper (D 8) (R 8) [6,65,288,48] 13 := by
  apply FastRouting.sound _ _ [6,65,288,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19038 c19038
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19038_9
  · exact m19038_33
  · exact u7719
  · exact u7720
  · exact u7721
  · exact u7722
  · exact u7723
  · exact u7724
  · exact u7725
  · exact u7726

def b19039 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 292 73 184 184 248 184 440), lower := (rows 7 67 292 73 16 32 64 128 256), losses := [] }

theorem u19039 : Upper (D 8) (R 8) [6,65,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19040_9 : Upper (D 8) (R 8) [6,65,288,80,9] 13 :=
  permutation_upper _ _ _ [6,65,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7708

theorem m19040_33 : Upper (D 8) (R 8) [6,65,288,80,33] 13 :=
  permutation_upper _ _ _ [6,65,288,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7714

theorem m19040_40 : Upper (D 8) (R 8) [6,65,288,80,40] 13 :=
  permutation_upper _ _ _ [6,65,288,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7721

def r19040 : Route 9 := (fun mask => (mask,id))

def c19040 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19040 : Upper (D 8) (R 8) [6,65,288,80] 13 := by
  apply FastRouting.sound _ _ [6,65,288,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19040 c19040
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19040_9
  · exact m19040_33
  · exact m19040_40
  · exact u7729
  · exact u7730
  · exact u7731

theorem m19041_9 : Upper (D 8) (R 8) [6,65,288,96,9] 13 :=
  permutation_upper _ _ _ [6,65,288,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7709

theorem m19041_33 : Upper (D 8) (R 8) [6,65,288,96,33] 13 :=
  permutation_upper _ _ _ [6,65,288,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7715

theorem m19041_40 : Upper (D 8) (R 8) [6,65,288,96,40] 13 :=
  permutation_upper _ _ _ [6,65,288,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7722

def r19041 : Route 9 := (fun mask => (mask,id))

def c19041 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19041 : Upper (D 8) (R 8) [6,65,288,96] 13 := by
  apply FastRouting.sound _ _ [6,65,288,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19041 c19041
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19041_9
  · exact m19041_33
  · exact m19041_40
  · exact u7732
  · exact u7733
  · exact u7734

def b19042 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 137 248 248 248 248 504), lower := (rows 7 67 292 137 16 32 64 128 256), losses := [] }

theorem u19042 : Upper (D 8) (R 8) [6,65,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19043_9 : Upper (D 8) (R 8) [6,65,288,144,9] 13 :=
  permutation_upper _ _ _ [6,65,288,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7710

theorem m19043_33 : Upper (D 8) (R 8) [6,65,288,144,33] 13 :=
  permutation_upper _ _ _ [6,65,288,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7716

theorem m19043_40 : Upper (D 8) (R 8) [6,65,288,144,40] 13 :=
  permutation_upper _ _ _ [6,65,288,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7724

theorem m19043_65 : Upper (D 8) (R 8) [6,65,288,144,65] 13 :=
  permutation_upper _ _ _ [6,65,288,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7727

theorem m19043_72 : Upper (D 8) (R 8) [6,65,288,144,72] 13 :=
  permutation_upper _ _ _ [6,65,288,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7730

theorem m19043_96 : Upper (D 8) (R 8) [6,65,288,144,96] 13 :=
  permutation_upper _ _ _ [6,65,288,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7733

theorem m19043_129 : Upper (D 8) (R 8) [6,65,288,144,129] 13 :=
  permutation_upper _ _ _ [6,65,288,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7735

def r19043 : Route 9 := (fun mask => (mask,id))

def c19043 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19043 : Upper (D 8) (R 8) [6,65,288,144] 13 := by
  apply FastRouting.sound _ _ [6,65,288,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19043 c19043
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19043_9
  · exact m19043_33
  · exact m19043_40
  · exact m19043_65
  · exact m19043_72
  · exact m19043_96
  · exact m19043_129
  · exact u7738
  · exact u7739
  · exact u7740

theorem m19044_9 : Upper (D 8) (R 8) [6,65,288,160,9] 13 :=
  permutation_upper _ _ _ [6,65,288,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7711

theorem m19044_33 : Upper (D 8) (R 8) [6,65,288,160,33] 13 :=
  permutation_upper _ _ _ [6,65,288,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7717

theorem m19044_40 : Upper (D 8) (R 8) [6,65,288,160,40] 13 :=
  permutation_upper _ _ _ [6,65,288,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7725

theorem m19044_65 : Upper (D 8) (R 8) [6,65,288,160,65] 13 :=
  permutation_upper _ _ _ [6,65,288,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7728

theorem m19044_72 : Upper (D 8) (R 8) [6,65,288,160,72] 13 :=
  permutation_upper _ _ _ [6,65,288,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7731

theorem m19044_96 : Upper (D 8) (R 8) [6,65,288,160,96] 13 :=
  permutation_upper _ _ _ [6,65,288,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7734

theorem m19044_129 : Upper (D 8) (R 8) [6,65,288,160,129] 13 :=
  permutation_upper _ _ _ [6,65,288,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7736

theorem m19044_136 : Upper (D 8) (R 8) [6,65,288,160,136] 13 :=
  permutation_upper _ _ _ [6,65,288,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7739

def r19044 : Route 9 := (fun mask => (mask,id))

def c19044 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19044 : Upper (D 8) (R 8) [6,65,288,160] 13 := by
  apply FastRouting.sound _ _ [6,65,288,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19044 c19044
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19044_9
  · exact m19044_33
  · exact m19044_40
  · exact m19044_65
  · exact m19044_72
  · exact m19044_96
  · exact m19044_129
  · exact m19044_136
  · exact u7741
  · exact u7742

theorem m19045_9 : Upper (D 8) (R 8) [6,65,288,192,9] 13 :=
  permutation_upper _ _ _ [6,65,288,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7712

theorem m19045_33 : Upper (D 8) (R 8) [6,65,288,192,33] 13 :=
  permutation_upper _ _ _ [6,65,288,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7718

theorem m19045_40 : Upper (D 8) (R 8) [6,65,288,192,40] 13 :=
  permutation_upper _ _ _ [6,65,288,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7726

theorem m19045_129 : Upper (D 8) (R 8) [6,65,288,192,129] 13 :=
  permutation_upper _ _ _ [6,65,288,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7737

theorem m19045_136 : Upper (D 8) (R 8) [6,65,288,192,136] 13 :=
  permutation_upper _ _ _ [6,65,288,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7740

theorem m19045_160 : Upper (D 8) (R 8) [6,65,288,192,160] 13 :=
  permutation_upper _ _ _ [6,65,288,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7742

def r19045 : Route 9 := (fun mask => (mask,id))

def c19045 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19045 : Upper (D 8) (R 8) [6,65,288,192] 13 := by
  apply FastRouting.sound _ _ [6,65,288,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19045 c19045
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19045_9
  · exact m19045_33
  · exact m19045_40
  · exact m19045_129
  · exact m19045_136
  · exact m19045_160

def b19046 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 25 248 232 232 232 488), lower := (rows 7 67 388 25 16 32 64 128 256), losses := [] }

theorem u19046 : Upper (D 8) (R 8) [6,65,384,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19047 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 41 248 248 248 248 504), lower := (rows 7 67 388 41 16 32 64 128 256), losses := [] }

theorem u19047 : Upper (D 8) (R 8) [6,65,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19048_9 : Upper (D 8) (R 8) [6,65,384,48,9] 13 :=
  permutation_upper _ _ _ [6,65,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7743

theorem m19048_33 : Upper (D 8) (R 8) [6,65,384,48,33] 13 :=
  permutation_upper _ _ _ [6,65,384,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7749

def r19048 : Route 9 := (fun mask => (mask,id))

def c19048 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19048 : Upper (D 8) (R 8) [6,65,384,48] 13 := by
  apply FastRouting.sound _ _ [6,65,384,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19048 c19048
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19048_9
  · exact m19048_33
  · exact u7755
  · exact u7756
  · exact u7757
  · exact u7758
  · exact u7759
  · exact u7760
  · exact u7761
  · exact u7762

def b19049 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 388 73 184 184 248 184 440), lower := (rows 7 67 388 73 16 32 64 128 256), losses := [] }

theorem u19049 : Upper (D 8) (R 8) [6,65,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19050_9 : Upper (D 8) (R 8) [6,65,384,80,9] 13 :=
  permutation_upper _ _ _ [6,65,384,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7744

theorem m19050_33 : Upper (D 8) (R 8) [6,65,384,80,33] 13 :=
  permutation_upper _ _ _ [6,65,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7750

theorem m19050_40 : Upper (D 8) (R 8) [6,65,384,80,40] 13 :=
  permutation_upper _ _ _ [6,65,384,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7757

def r19050 : Route 9 := (fun mask => (mask,id))

def c19050 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19050 : Upper (D 8) (R 8) [6,65,384,80] 13 := by
  apply FastRouting.sound _ _ [6,65,384,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19050 c19050
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19050_9
  · exact m19050_33
  · exact m19050_40
  · exact u7765
  · exact u7766
  · exact u7767

theorem m19051_9 : Upper (D 8) (R 8) [6,65,384,96,9] 13 :=
  permutation_upper _ _ _ [6,65,384,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7745

theorem m19051_33 : Upper (D 8) (R 8) [6,65,384,96,33] 13 :=
  permutation_upper _ _ _ [6,65,384,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7751

theorem m19051_40 : Upper (D 8) (R 8) [6,65,384,96,40] 13 :=
  permutation_upper _ _ _ [6,65,384,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7758

def r19051 : Route 9 := (fun mask => (mask,id))

def c19051 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19051 : Upper (D 8) (R 8) [6,65,384,96] 13 := by
  apply FastRouting.sound _ _ [6,65,384,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19051 c19051
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19051_9
  · exact m19051_33
  · exact m19051_40
  · exact u7768
  · exact u7769
  · exact u7770

def b19052 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 137 120 120 120 248 376), lower := (rows 7 67 388 137 16 32 64 128 256), losses := [] }

theorem u19052 : Upper (D 8) (R 8) [6,65,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19053_9 : Upper (D 8) (R 8) [6,65,384,144,9] 13 :=
  permutation_upper _ _ _ [6,65,384,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7746

theorem m19053_33 : Upper (D 8) (R 8) [6,65,384,144,33] 13 :=
  permutation_upper _ _ _ [6,65,384,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7752

theorem m19053_40 : Upper (D 8) (R 8) [6,65,384,144,40] 13 :=
  permutation_upper _ _ _ [6,65,384,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7760

theorem m19053_65 : Upper (D 8) (R 8) [6,65,384,144,65] 13 :=
  permutation_upper _ _ _ [6,65,384,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7763

theorem m19053_72 : Upper (D 8) (R 8) [6,65,384,144,72] 13 :=
  permutation_upper _ _ _ [6,65,384,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7766

theorem m19053_96 : Upper (D 8) (R 8) [6,65,384,144,96] 13 :=
  permutation_upper _ _ _ [6,65,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7769

def r19053 : Route 9 := (fun mask => (mask,id))

def c19053 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19053 : Upper (D 8) (R 8) [6,65,384,144] 13 := by
  apply FastRouting.sound _ _ [6,65,384,144] 13 (by decide) (choices 2) [9,33,40,65,72,96] r19053 c19053
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19053_9
  · exact m19053_33
  · exact m19053_40
  · exact m19053_65
  · exact m19053_72
  · exact m19053_96

theorem m19054_9 : Upper (D 8) (R 8) [6,65,384,160,9] 13 :=
  permutation_upper _ _ _ [6,65,384,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7747

theorem m19054_33 : Upper (D 8) (R 8) [6,65,384,160,33] 13 :=
  permutation_upper _ _ _ [6,65,384,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7753

theorem m19054_40 : Upper (D 8) (R 8) [6,65,384,160,40] 13 :=
  permutation_upper _ _ _ [6,65,384,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7761

theorem m19054_65 : Upper (D 8) (R 8) [6,65,384,160,65] 13 :=
  permutation_upper _ _ _ [6,65,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7764

theorem m19054_72 : Upper (D 8) (R 8) [6,65,384,160,72] 13 :=
  permutation_upper _ _ _ [6,65,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7767

theorem m19054_96 : Upper (D 8) (R 8) [6,65,384,160,96] 13 :=
  permutation_upper _ _ _ [6,65,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7770

def r19054 : Route 9 := (fun mask => (mask,id))

def c19054 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19054 : Upper (D 8) (R 8) [6,65,384,160] 13 := by
  apply FastRouting.sound _ _ [6,65,384,160] 13 (by decide) (choices 2) [9,33,40,65,72,96] r19054 c19054
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19054_9
  · exact m19054_33
  · exact m19054_40
  · exact m19054_65
  · exact m19054_72
  · exact m19054_96

theorem m19055_9 : Upper (D 8) (R 8) [6,65,384,192,9] 13 :=
  permutation_upper _ _ _ [6,65,384,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7748

theorem m19055_33 : Upper (D 8) (R 8) [6,65,384,192,33] 13 :=
  permutation_upper _ _ _ [6,65,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7754

theorem m19055_40 : Upper (D 8) (R 8) [6,65,384,192,40] 13 :=
  permutation_upper _ _ _ [6,65,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7762

def r19055 : Route 9 := (fun mask => (mask,id))

def c19055 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u19055 : Upper (D 8) (R 8) [6,65,384,192] 13 := by
  apply FastRouting.sound _ _ [6,65,384,192] 13 (by decide) (choices 2) [9,33,40] r19055 c19055
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m19055_9
  · exact m19055_33
  · exact m19055_40

def r19056 : Route 9 := (fun mask => (mask,id))

def c19056 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19056 : Upper (D 8) (R 8) [6,72,144,33] 13 := by
  apply FastRouting.sound _ _ [6,72,144,33] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19056 c19056
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7771
  · exact u7772
  · exact u7773
  · exact u7774
  · exact u7775
  · exact u7776
  · exact u7777
  · exact u7778
  · exact u7779
  · exact u7780

def b19057 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 148 73 433 417 481 417 417), lower := (rows 7 74 148 73 16 32 64 128 256), losses := [] }

theorem u19057 : Upper (D 8) (R 8) [6,72,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19058 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 148 104 433 417 481 417 417), lower := (rows 7 74 148 104 16 32 64 128 256), losses := [] }

theorem u19058 : Upper (D 8) (R 8) [6,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19059 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 148 137 369 353 353 481 353), lower := (rows 7 74 148 137 16 32 64 128 256), losses := [] }

theorem u19059 : Upper (D 8) (R 8) [6,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19060 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 148 168 369 353 353 481 353), lower := (rows 7 74 148 168 16 32 64 128 256), losses := [] }

theorem u19060 : Upper (D 8) (R 8) [6,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19061 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 148 200 305 289 353 417 289), lower := (rows 7 74 148 200 16 32 64 128 256), losses := [] }

theorem u19061 : Upper (D 8) (R 8) [6,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19062_33 : Upper (D 8) (R 8) [6,72,144,257,33] 13 :=
  permutation_upper _ _ _ [6,72,144,33,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7777

theorem m19062_65 : Upper (D 8) (R 8) [6,72,144,257,65] 13 :=
  permutation_upper _ _ _ [6,72,144,129,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7785

theorem m19062_96 : Upper (D 8) (R 8) [6,72,144,257,96] 13 :=
  permutation_upper _ _ _ [6,72,144,160,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7787

theorem m19062_129 : Upper (D 8) (R 8) [6,72,144,257,129] 13 :=
  permutation_upper _ _ _ [6,72,144,65,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7781

theorem m19062_160 : Upper (D 8) (R 8) [6,72,144,257,160] 13 :=
  permutation_upper _ _ _ [6,72,144,96,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7783

theorem m19062_192 : Upper (D 8) (R 8) [6,72,144,257,192] 13 :=
  permutation_upper _ _ _ [6,72,144,192,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7789

def r19062 : Route 9 := (fun mask => (mask,id))

def c19062 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19062 : Upper (D 8) (R 8) [6,72,144,257] 13 := by
  apply FastRouting.sound _ _ [6,72,144,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19062 c19062
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19062_33
  · exact m19062_65
  · exact m19062_96
  · exact m19062_129
  · exact m19062_160
  · exact m19062_192

theorem m19063_33 : Upper (D 8) (R 8) [6,72,144,288,33] 13 :=
  permutation_upper _ _ _ [6,72,144,33,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7778

theorem m19063_65 : Upper (D 8) (R 8) [6,72,144,288,65] 13 :=
  permutation_upper _ _ _ [6,72,144,129,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7786

theorem m19063_96 : Upper (D 8) (R 8) [6,72,144,288,96] 13 :=
  permutation_upper _ _ _ [6,72,144,160,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7788

theorem m19063_129 : Upper (D 8) (R 8) [6,72,144,288,129] 13 :=
  permutation_upper _ _ _ [6,72,144,65,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7782

theorem m19063_160 : Upper (D 8) (R 8) [6,72,144,288,160] 13 :=
  permutation_upper _ _ _ [6,72,144,96,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7784

theorem m19063_192 : Upper (D 8) (R 8) [6,72,144,288,192] 13 :=
  permutation_upper _ _ _ [6,72,144,192,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7790

def r19063 : Route 9 := (fun mask => (mask,id))

def c19063 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19063 : Upper (D 8) (R 8) [6,72,144,288] 13 := by
  apply FastRouting.sound _ _ [6,72,144,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19063 c19063
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19063_33
  · exact m19063_65
  · exact m19063_96
  · exact m19063_129
  · exact m19063_160
  · exact m19063_192

def b19064 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 181, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 148 328 177 161 225 161 417), lower := (rows 7 74 148 328 16 32 64 128 256), losses := [] }

theorem u19064 : Upper (D 8) (R 8) [6,72,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19065 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 112, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 148 392 113 97 97 225 353), lower := (rows 7 74 148 392 16 32 64 128 256), losses := [] }

theorem u19065 : Upper (D 8) (R 8) [6,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19066 : Route 9 := (fun mask => (mask,id))

def c19066 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19066 : Upper (D 8) (R 8) [6,72,160,17] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19066 c19066
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7791
  · exact u7792
  · exact u7793
  · exact u7794
  · exact u7795
  · exact u7796
  · exact u7797
  · exact u7798
  · exact u7799
  · exact u7800

def r19067 : Route 9 := (fun mask => (mask,id))

def c19067 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19067 : Upper (D 8) (R 8) [6,72,160,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19067 c19067
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7801
  · exact u7802
  · exact u7803
  · exact u7804
  · exact u7805
  · exact u7806
  · exact u7807
  · exact u7808
  · exact u7809
  · exact u7810

def r19068 : Route 9 := (fun mask => (mask,id))

def c19068 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19068 : Upper (D 8) (R 8) [6,72,160,48] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19068 c19068
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7811
  · exact u7812
  · exact u7813
  · exact u7814
  · exact u7815
  · exact u7816
  · exact u7817
  · exact u7818
  · exact u7819
  · exact u7820

def b19069 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 73 433 433 497 433 433), lower := (rows 7 74 164 73 16 32 64 128 256), losses := [] }

theorem u19069 : Upper (D 8) (R 8) [6,72,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19070 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 88 433 417 481 417 417), lower := (rows 7 74 164 88 16 32 64 128 256), losses := [] }

theorem u19070 : Upper (D 8) (R 8) [6,72,160,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19071 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 104 433 433 497 433 433), lower := (rows 7 74 164 104 16 32 64 128 256), losses := [] }

theorem u19071 : Upper (D 8) (R 8) [6,72,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19072 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 164 137 369 369 369 497 369), lower := (rows 7 74 164 137 16 32 64 128 256), losses := [] }

theorem u19072 : Upper (D 8) (R 8) [6,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19073 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 164 152 369 353 353 481 353), lower := (rows 7 74 164 152 16 32 64 128 256), losses := [] }

theorem u19073 : Upper (D 8) (R 8) [6,72,160,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19074 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 74 164 168 369 369 369 497 369), lower := (rows 7 74 164 168 16 32 64 128 256), losses := [] }

theorem u19074 : Upper (D 8) (R 8) [6,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19075 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 200 305 305 369 433 305), lower := (rows 7 74 164 200 16 32 64 128 256), losses := [] }

theorem u19075 : Upper (D 8) (R 8) [6,72,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19076 : Route 9 := (fun mask => (mask,id))

def c19076 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19076 : Upper (D 8) (R 8) [6,72,160,257] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19076 c19076
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7821
  · exact u7822
  · exact u7823
  · exact u7824
  · exact u7825
  · exact u7826

def r19077 : Route 9 := (fun mask => (mask,id))

def c19077 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19077 : Upper (D 8) (R 8) [6,72,160,272] 13 := by
  apply FastRouting.sound _ _ [6,72,160,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19077 c19077
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7827
  · exact u7828
  · exact u7829
  · exact u7830
  · exact u7831
  · exact u7832

def r19078 : Route 9 := (fun mask => (mask,id))

def c19078 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19078 : Upper (D 8) (R 8) [6,72,160,288] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19078 c19078
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7833
  · exact u7834
  · exact u7835
  · exact u7836
  · exact u7837
  · exact u7838

def b19079 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 181, targets := 64 }], pairs := [(0,6)], upper := (rows 7 74 164 328 177 177 241 177 433), lower := (rows 7 74 164 328 16 32 64 128 256), losses := [] }

theorem u19079 : Upper (D 8) (R 8) [6,72,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19079 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u19079
end Delivery.IrregularNine14.P08
