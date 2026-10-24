import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0124
import IrregularNine14P09C0125
import IrregularNine14P09C0126
import IrregularNine14P09C0127
import IrregularNine14P09C0128
import IrregularNine14P09C0129

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m9060_9 : Upper (D 9) (R 9) [34,68,129,96,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7480

def r9060 : Route 9 := (fun mask => (mask,id))

def c9060 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9060 : Upper (D 9) (R 9) [34,68,129,96] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96] 13 (by decide) (choices 2) [9,129,136,257,264,384] r9060 c9060
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9060_9
  · exact u7515
  · exact u7516
  · exact u7517
  · exact u7518
  · exact u7519

def b9061 : PairBound 9 := { available := 376, camps := [{ cop := 2, region := 8, targets := 352 },{ cop := 3, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6),(3,8)], upper := (rows 35 70 133 137 376 376 376 504 376), lower := (rows 35 70 133 137 16 32 64 128 256), losses := [] }

theorem u9061 : Upper (D 9) (R 9) [34,68,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9061 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9062_9 : Upper (D 9) (R 9) [34,68,129,144,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7481

theorem m9062_33 : Upper (D 9) (R 9) [34,68,129,144,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7489

theorem m9062_40 : Upper (D 9) (R 9) [34,68,129,144,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7497

theorem m9062_65 : Upper (D 9) (R 9) [34,68,129,144,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7503

theorem m9062_72 : Upper (D 9) (R 9) [34,68,129,144,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7509

theorem m9062_96 : Upper (D 9) (R 9) [34,68,129,144,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7516

def r9062 : Route 9 := (fun mask => (mask,id))

def c9062 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9062 : Upper (D 9) (R 9) [34,68,129,144] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r9062 c9062
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9062_9
  · exact m9062_33
  · exact m9062_40
  · exact m9062_65
  · exact m9062_72
  · exact m9062_96
  · exact u7523
  · exact u7524
  · exact u7525
  · exact u7526

theorem m9063_9 : Upper (D 9) (R 9) [34,68,129,160,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7482

theorem m9063_65 : Upper (D 9) (R 9) [34,68,129,160,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7504

theorem m9063_72 : Upper (D 9) (R 9) [34,68,129,160,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7510

def r9063 : Route 9 := (fun mask => (mask,id))

def c9063 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9063 : Upper (D 9) (R 9) [34,68,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160] 13 (by decide) (choices 2) [9,65,72,257,264,320] r9063 c9063
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9063_9
  · exact m9063_65
  · exact m9063_72
  · exact u7527
  · exact u7528
  · exact u7529

theorem m9064_9 : Upper (D 9) (R 9) [34,68,129,192,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7483

theorem m9064_33 : Upper (D 9) (R 9) [34,68,129,192,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7490

theorem m9064_40 : Upper (D 9) (R 9) [34,68,129,192,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7498

def r9064 : Route 9 := (fun mask => (mask,id))

def c9064 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9064 : Upper (D 9) (R 9) [34,68,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r9064 c9064
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9064_9
  · exact m9064_33
  · exact m9064_40
  · exact u7530
  · exact u7531
  · exact u7532

theorem m9065_40 : Upper (D 9) (R 9) [34,68,129,257,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7499

theorem m9065_72 : Upper (D 9) (R 9) [34,68,129,257,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7511

theorem m9065_96 : Upper (D 9) (R 9) [34,68,129,257,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7517

theorem m9065_136 : Upper (D 9) (R 9) [34,68,129,257,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7523

theorem m9065_160 : Upper (D 9) (R 9) [34,68,129,257,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7527

theorem m9065_192 : Upper (D 9) (R 9) [34,68,129,257,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7530

def r9065 : Route 9 := (fun mask => (mask,id))

def c9065 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9065 : Upper (D 9) (R 9) [34,68,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,257] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r9065 c9065
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9065_40
  · exact m9065_72
  · exact m9065_96
  · exact m9065_136
  · exact m9065_160
  · exact m9065_192
  · exact u7533
  · exact u7534
  · exact u7535
  · exact u7536

theorem m9066_9 : Upper (D 9) (R 9) [34,68,129,272,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7484

theorem m9066_33 : Upper (D 9) (R 9) [34,68,129,272,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7491

theorem m9066_40 : Upper (D 9) (R 9) [34,68,129,272,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7500

theorem m9066_65 : Upper (D 9) (R 9) [34,68,129,272,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7505

theorem m9066_72 : Upper (D 9) (R 9) [34,68,129,272,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7512

theorem m9066_96 : Upper (D 9) (R 9) [34,68,129,272,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7518

theorem m9066_129 : Upper (D 9) (R 9) [34,68,129,272,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7520

theorem m9066_136 : Upper (D 9) (R 9) [34,68,129,272,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7524

theorem m9066_160 : Upper (D 9) (R 9) [34,68,129,272,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7528

theorem m9066_192 : Upper (D 9) (R 9) [34,68,129,272,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7531

theorem m9066_257 : Upper (D 9) (R 9) [34,68,129,272,257] 13 :=
  permutation_upper _ _ _ [34,68,129,257,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7533

def r9066 : Route 9 := (fun mask => (mask,id))

def c9066 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9066 : Upper (D 9) (R 9) [34,68,129,272] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r9066 c9066
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9066_9
  · exact m9066_33
  · exact m9066_40
  · exact m9066_65
  · exact m9066_72
  · exact m9066_96
  · exact m9066_129
  · exact m9066_136
  · exact m9066_160
  · exact m9066_192
  · exact m9066_257
  · exact u7537
  · exact u7538
  · exact u7539
  · exact u7540

theorem m9067_9 : Upper (D 9) (R 9) [34,68,129,288,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7485

theorem m9067_65 : Upper (D 9) (R 9) [34,68,129,288,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7506

theorem m9067_72 : Upper (D 9) (R 9) [34,68,129,288,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7513

theorem m9067_129 : Upper (D 9) (R 9) [34,68,129,288,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7521

theorem m9067_136 : Upper (D 9) (R 9) [34,68,129,288,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7525

theorem m9067_192 : Upper (D 9) (R 9) [34,68,129,288,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7532

theorem m9067_257 : Upper (D 9) (R 9) [34,68,129,288,257] 13 :=
  permutation_upper _ _ _ [34,68,129,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7534

theorem m9067_264 : Upper (D 9) (R 9) [34,68,129,288,264] 13 :=
  permutation_upper _ _ _ [34,68,129,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7538

def r9067 : Route 9 := (fun mask => (mask,id))

def c9067 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9067 : Upper (D 9) (R 9) [34,68,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,288] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r9067 c9067
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9067_9
  · exact m9067_65
  · exact m9067_72
  · exact m9067_129
  · exact m9067_136
  · exact m9067_192
  · exact m9067_257
  · exact m9067_264
  · exact u7541
  · exact u7542

theorem m9068_9 : Upper (D 9) (R 9) [34,68,129,320,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7486

theorem m9068_33 : Upper (D 9) (R 9) [34,68,129,320,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7492

theorem m9068_40 : Upper (D 9) (R 9) [34,68,129,320,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7501

theorem m9068_129 : Upper (D 9) (R 9) [34,68,129,320,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7522

theorem m9068_136 : Upper (D 9) (R 9) [34,68,129,320,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7526

theorem m9068_160 : Upper (D 9) (R 9) [34,68,129,320,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7529

theorem m9068_257 : Upper (D 9) (R 9) [34,68,129,320,257] 13 :=
  permutation_upper _ _ _ [34,68,129,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7535

theorem m9068_264 : Upper (D 9) (R 9) [34,68,129,320,264] 13 :=
  permutation_upper _ _ _ [34,68,129,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7539

theorem m9068_288 : Upper (D 9) (R 9) [34,68,129,320,288] 13 :=
  permutation_upper _ _ _ [34,68,129,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7541

def r9068 : Route 9 := (fun mask => (mask,id))

def c9068 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9068 : Upper (D 9) (R 9) [34,68,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,320] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r9068 c9068
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9068_9
  · exact m9068_33
  · exact m9068_40
  · exact m9068_129
  · exact m9068_136
  · exact m9068_160
  · exact m9068_257
  · exact m9068_264
  · exact m9068_288
  · exact u7543

theorem m9069_9 : Upper (D 9) (R 9) [34,68,129,384,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7487

theorem m9069_33 : Upper (D 9) (R 9) [34,68,129,384,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7493

theorem m9069_40 : Upper (D 9) (R 9) [34,68,129,384,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7502

theorem m9069_65 : Upper (D 9) (R 9) [34,68,129,384,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7507

theorem m9069_72 : Upper (D 9) (R 9) [34,68,129,384,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7514

theorem m9069_96 : Upper (D 9) (R 9) [34,68,129,384,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7519

theorem m9069_257 : Upper (D 9) (R 9) [34,68,129,384,257] 13 :=
  permutation_upper _ _ _ [34,68,129,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7536

theorem m9069_264 : Upper (D 9) (R 9) [34,68,129,384,264] 13 :=
  permutation_upper _ _ _ [34,68,129,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7540

theorem m9069_288 : Upper (D 9) (R 9) [34,68,129,384,288] 13 :=
  permutation_upper _ _ _ [34,68,129,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7542

theorem m9069_320 : Upper (D 9) (R 9) [34,68,129,384,320] 13 :=
  permutation_upper _ _ _ [34,68,129,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7543

def r9069 : Route 9 := (fun mask => (mask,id))

def c9069 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9069 : Upper (D 9) (R 9) [34,68,129,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,384] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r9069 c9069
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9069_9
  · exact m9069_33
  · exact m9069_40
  · exact m9069_65
  · exact m9069_72
  · exact m9069_96
  · exact m9069_257
  · exact m9069_264
  · exact m9069_288
  · exact m9069_320

def r9070 : Route 9 := (fun mask => (mask,id))

def c9070 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9070 : Upper (D 9) (R 9) [34,68,136,17] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r9070 c9070
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7544
  · exact u7545
  · exact u7546
  · exact u7547
  · exact u7548
  · exact u7549
  · exact u7550
  · exact u7551
  · exact u7552
  · exact u7553

def b9071 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 140 41 465 497 465 465 465), lower := (rows 35 70 140 41 16 32 64 128 256), losses := [] }

theorem u9071 : Upper (D 9) (R 9) [34,68,136,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9071 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r9072 : Route 9 := (fun mask => (mask,id))

def c9072 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9072 : Upper (D 9) (R 9) [34,68,136,48] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48] 13 (by decide) (choices 2) [65,129,192,257,320,384] r9072 c9072
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7554
  · exact u7555
  · exact u7556
  · exact u7557
  · exact u7558
  · exact u7559

def r9073 : Route 9 := (fun mask => (mask,id))

def c9073 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9073 : Upper (D 9) (R 9) [34,68,136,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,65] 13 (by decide) (choices 2) [33,129,160,257,288,384] r9073 c9073
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7560
  · exact u7561
  · exact u7562
  · exact u7563
  · exact u7564
  · exact u7565

def r9074 : Route 9 := (fun mask => (mask,id))

def c9074 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9074 : Upper (D 9) (R 9) [34,68,136,80] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80] 13 (by decide) (choices 2) [33,129,160,257,288,384] r9074 c9074
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7566
  · exact u7567
  · exact u7568
  · exact u7569
  · exact u7570
  · exact u7571

def r9075 : Route 9 := (fun mask => (mask,id))

def c9075 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9075 : Upper (D 9) (R 9) [34,68,136,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,96] 13 (by decide) (choices 2) [129,257,384] r9075 c9075
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7572
  · exact u7573
  · exact u7574

def b9076 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 70 140 137 369 369 369 497 369), lower := (rows 35 70 140 137 16 32 64 128 256), losses := [] }

theorem u9076 : Upper (D 9) (R 9) [34,68,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9076 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9077 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 70 140 152 369 353 353 481 353), lower := (rows 35 70 140 152 16 32 64 128 256), losses := [] }

theorem u9077 : Upper (D 9) (R 9) [34,68,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9077 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9078 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 70 140 168 337 369 337 465 337), lower := (rows 35 70 140 168 16 32 64 128 256), losses := [] }

theorem u9078 : Upper (D 9) (R 9) [34,68,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9078 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9079 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 6, targets := 289 }], pairs := [(1,0),(1,5),(1,8),(2,0),(2,5)], upper := (rows 35 70 140 200 305 305 369 433 305), lower := (rows 35 70 140 200 16 32 64 128 256), losses := [] }

theorem u9079 : Upper (D 9) (R 9) [34,68,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9079 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r9080 : Route 9 := (fun mask => (mask,id))

def c9080 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9080 : Upper (D 9) (R 9) [34,68,136,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r9080 c9080
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7575
  · exact u7576
  · exact u7577
  · exact u7578
  · exact u7579
  · exact u7580
  · exact u7581
  · exact u7582
  · exact u7583
  · exact u7584

def r9081 : Route 9 := (fun mask => (mask,id))

def c9081 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9081 : Upper (D 9) (R 9) [34,68,136,272] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r9081 c9081
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7585
  · exact u7586
  · exact u7587
  · exact u7588
  · exact u7589
  · exact u7590
  · exact u7591
  · exact u7592
  · exact u7593
  · exact u7594

def r9082 : Route 9 := (fun mask => (mask,id))

def c9082 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9082 : Upper (D 9) (R 9) [34,68,136,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288] 13 (by decide) (choices 2) [65,129,192,257,320,384] r9082 c9082
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7595
  · exact u7596
  · exact u7597
  · exact u7598
  · exact u7599
  · exact u7600

def r9083 : Route 9 := (fun mask => (mask,id))

def c9083 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9083 : Upper (D 9) (R 9) [34,68,136,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,320] 13 (by decide) (choices 2) [33,129,160,257,288,384] r9083 c9083
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7601
  · exact u7602
  · exact u7603
  · exact u7604
  · exact u7605
  · exact u7606

def b9084 : PairBound 9 := { available := 369, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 35 70 140 392 369 369 369 497 369), lower := (rows 35 70 140 392 16 32 64 128 256), losses := [] }

theorem u9084 : Upper (D 9) (R 9) [34,68,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9084 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r9085 : Route 9 := (fun mask => (mask,id))

def c9085 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9085 : Upper (D 9) (R 9) [34,68,160,17] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r9085 c9085
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7607
  · exact u7608
  · exact u7609
  · exact u7610
  · exact u7611
  · exact u7612
  · exact u7613
  · exact u7614
  · exact u7615
  · exact u7616

theorem m9086_9 : Upper (D 9) (R 9) [34,68,160,65,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7608

def r9086 : Route 9 := (fun mask => (mask,id))

def c9086 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9086 : Upper (D 9) (R 9) [34,68,160,65] 13 := by
  apply FastRouting.sound _ _ [34,68,160,65] 13 (by decide) (choices 2) [9,129,136,257,264,384] r9086 c9086
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9086_9
  · exact u7617
  · exact u7618
  · exact u7619
  · exact u7620
  · exact u7621

theorem m9087_9 : Upper (D 9) (R 9) [34,68,160,80,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7609

def r9087 : Route 9 := (fun mask => (mask,id))

def c9087 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9087 : Upper (D 9) (R 9) [34,68,160,80] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80] 13 (by decide) (choices 2) [9,129,136,257,264,384] r9087 c9087
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9087_9
  · exact u7622
  · exact u7623
  · exact u7624
  · exact u7625
  · exact u7626

theorem m9088_9 : Upper (D 9) (R 9) [34,68,160,129,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7610

theorem m9088_65 : Upper (D 9) (R 9) [34,68,160,129,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7617

theorem m9088_72 : Upper (D 9) (R 9) [34,68,160,129,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7622

def r9088 : Route 9 := (fun mask => (mask,id))

def c9088 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9088 : Upper (D 9) (R 9) [34,68,160,129] 13 := by
  apply FastRouting.sound _ _ [34,68,160,129] 13 (by decide) (choices 2) [9,65,72,257,264,320] r9088 c9088
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9088_9
  · exact m9088_65
  · exact m9088_72
  · exact u7627
  · exact u7628
  · exact u7629

theorem m9089_9 : Upper (D 9) (R 9) [34,68,160,144,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7611

theorem m9089_65 : Upper (D 9) (R 9) [34,68,160,144,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7618

theorem m9089_72 : Upper (D 9) (R 9) [34,68,160,144,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7623

def r9089 : Route 9 := (fun mask => (mask,id))

def c9089 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9089 : Upper (D 9) (R 9) [34,68,160,144] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144] 13 (by decide) (choices 2) [9,65,72,257,264,320] r9089 c9089
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9089_9
  · exact m9089_65
  · exact m9089_72
  · exact u7630
  · exact u7631
  · exact u7632

theorem m9090_9 : Upper (D 9) (R 9) [34,68,160,192,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7612

def r9090 : Route 9 := (fun mask => (mask,id))

def c9090 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9090 : Upper (D 9) (R 9) [34,68,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192] 13 (by decide) (choices 2) [9,257,264] r9090 c9090
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m9090_9
  · exact u7633
  · exact u7634

theorem m9091_9 : Upper (D 9) (R 9) [34,68,160,257,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7613

theorem m9091_65 : Upper (D 9) (R 9) [34,68,160,257,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7619

theorem m9091_72 : Upper (D 9) (R 9) [34,68,160,257,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7624

theorem m9091_129 : Upper (D 9) (R 9) [34,68,160,257,129] 13 :=
  permutation_upper _ _ _ [34,68,160,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7627

theorem m9091_136 : Upper (D 9) (R 9) [34,68,160,257,136] 13 :=
  permutation_upper _ _ _ [34,68,160,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7630

theorem m9091_192 : Upper (D 9) (R 9) [34,68,160,257,192] 13 :=
  permutation_upper _ _ _ [34,68,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7633

def r9091 : Route 9 := (fun mask => (mask,id))

def c9091 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9091 : Upper (D 9) (R 9) [34,68,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,160,257] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r9091 c9091
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9091_9
  · exact m9091_65
  · exact m9091_72
  · exact m9091_129
  · exact m9091_136
  · exact m9091_192
  · exact u7635
  · exact u7636
  · exact u7637
  · exact u7638

theorem m9092_9 : Upper (D 9) (R 9) [34,68,160,272,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7614

theorem m9092_65 : Upper (D 9) (R 9) [34,68,160,272,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7620

theorem m9092_72 : Upper (D 9) (R 9) [34,68,160,272,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7625

theorem m9092_129 : Upper (D 9) (R 9) [34,68,160,272,129] 13 :=
  permutation_upper _ _ _ [34,68,160,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7628

theorem m9092_136 : Upper (D 9) (R 9) [34,68,160,272,136] 13 :=
  permutation_upper _ _ _ [34,68,160,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7631

theorem m9092_192 : Upper (D 9) (R 9) [34,68,160,272,192] 13 :=
  permutation_upper _ _ _ [34,68,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7634

theorem m9092_257 : Upper (D 9) (R 9) [34,68,160,272,257] 13 :=
  permutation_upper _ _ _ [34,68,160,257,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7636

def r9092 : Route 9 := (fun mask => (mask,id))

def c9092 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9092 : Upper (D 9) (R 9) [34,68,160,272] 13 := by
  apply FastRouting.sound _ _ [34,68,160,272] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r9092 c9092
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9092_9
  · exact m9092_65
  · exact m9092_72
  · exact m9092_129
  · exact m9092_136
  · exact m9092_192
  · exact m9092_257
  · exact u7639
  · exact u7640
  · exact u7641

theorem m9093_9 : Upper (D 9) (R 9) [34,68,160,320,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7615

theorem m9093_129 : Upper (D 9) (R 9) [34,68,160,320,129] 13 :=
  permutation_upper _ _ _ [34,68,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7629

theorem m9093_136 : Upper (D 9) (R 9) [34,68,160,320,136] 13 :=
  permutation_upper _ _ _ [34,68,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7632

theorem m9093_257 : Upper (D 9) (R 9) [34,68,160,320,257] 13 :=
  permutation_upper _ _ _ [34,68,160,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7637

theorem m9093_264 : Upper (D 9) (R 9) [34,68,160,320,264] 13 :=
  permutation_upper _ _ _ [34,68,160,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7640

def r9093 : Route 9 := (fun mask => (mask,id))

def c9093 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9093 : Upper (D 9) (R 9) [34,68,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,160,320] 13 (by decide) (choices 2) [9,129,136,257,264,384] r9093 c9093
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9093_9
  · exact m9093_129
  · exact m9093_136
  · exact m9093_257
  · exact m9093_264
  · exact u7642

theorem m9094_9 : Upper (D 9) (R 9) [34,68,160,384,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7616

theorem m9094_65 : Upper (D 9) (R 9) [34,68,160,384,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7621

theorem m9094_72 : Upper (D 9) (R 9) [34,68,160,384,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7626

theorem m9094_257 : Upper (D 9) (R 9) [34,68,160,384,257] 13 :=
  permutation_upper _ _ _ [34,68,160,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7638

theorem m9094_264 : Upper (D 9) (R 9) [34,68,160,384,264] 13 :=
  permutation_upper _ _ _ [34,68,160,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7641

theorem m9094_320 : Upper (D 9) (R 9) [34,68,160,384,320] 13 :=
  permutation_upper _ _ _ [34,68,160,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7642

def r9094 : Route 9 := (fun mask => (mask,id))

def c9094 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9094 : Upper (D 9) (R 9) [34,68,160,384] 13 := by
  apply FastRouting.sound _ _ [34,68,160,384] 13 (by decide) (choices 2) [9,65,72,257,264,320] r9094 c9094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9094_9
  · exact m9094_65
  · exact m9094_72
  · exact m9094_257
  · exact m9094_264
  · exact m9094_320

def r9095 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9095 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9095 : Upper (D 9) (R 9) [34,68,384,17] 13 := by
  apply FastRouting.sound _ _ [34,68,384,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,384] r9095 c9095
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7643
  · exact u7644
  · exact u7645
  · exact u7646
  · exact u7647
  · exact u7648
  · exact u7649
  · exact u7650
  · exact u7651
  · exact u7652
  · exact u7653

def b9096 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 35 70 388 41 473 505 473 473 473), lower := (rows 35 70 388 41 16 32 64 128 256), losses := [] }

theorem u9096 : Upper (D 9) (R 9) [34,68,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9096 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9097_9 : Upper (D 9) (R 9) [34,68,384,48,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7645

def r9097 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9097 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9097 : Upper (D 9) (R 9) [34,68,384,48] 13 := by
  apply FastRouting.sound _ _ [34,68,384,48] 13 (by decide) (choices 2) [9,65,72,129,136,192,384] r9097 c9097
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9097_9
  · exact u7659
  · exact u7660
  · exact u7661
  · exact u7662
  · exact u7663
  · exact u7664

theorem m9098_9 : Upper (D 9) (R 9) [34,68,384,65,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7646

theorem m9098_33 : Upper (D 9) (R 9) [34,68,384,65,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7654

theorem m9098_40 : Upper (D 9) (R 9) [34,68,384,65,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7659

def r9098 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9098 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9098 : Upper (D 9) (R 9) [34,68,384,65] 13 := by
  apply FastRouting.sound _ _ [34,68,384,65] 13 (by decide) (choices 2) [9,33,40,129,136,160,384] r9098 c9098
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9098_9
  · exact m9098_33
  · exact m9098_40
  · exact u7665
  · exact u7666
  · exact u7667
  · exact u7668

theorem m9099_9 : Upper (D 9) (R 9) [34,68,384,80,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7647

theorem m9099_33 : Upper (D 9) (R 9) [34,68,384,80,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7655

theorem m9099_40 : Upper (D 9) (R 9) [34,68,384,80,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7660

def r9099 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9099 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9099 : Upper (D 9) (R 9) [34,68,384,80] 13 := by
  apply FastRouting.sound _ _ [34,68,384,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,384] r9099 c9099
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9099_9
  · exact m9099_33
  · exact m9099_40
  · exact u7669
  · exact u7670
  · exact u7671
  · exact u7672

theorem m9100_9 : Upper (D 9) (R 9) [34,68,384,96,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7648

def r9100 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9100 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9100 : Upper (D 9) (R 9) [34,68,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,384,96] 13 (by decide) (choices 2) [9,129,136,384] r9100 c9100
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m9100_9
  · exact u7673
  · exact u7674
  · exact u7675

theorem m9101_9 : Upper (D 9) (R 9) [34,68,384,129,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7649

theorem m9101_33 : Upper (D 9) (R 9) [34,68,384,129,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7656

theorem m9101_40 : Upper (D 9) (R 9) [34,68,384,129,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7661

theorem m9101_65 : Upper (D 9) (R 9) [34,68,384,129,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7665

theorem m9101_72 : Upper (D 9) (R 9) [34,68,384,129,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7669

theorem m9101_96 : Upper (D 9) (R 9) [34,68,384,129,96] 13 :=
  permutation_upper _ _ _ [34,68,384,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7673

def r9101 : Route 9 := (fun mask => (mask,id))

def c9101 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9101 : Upper (D 9) (R 9) [34,68,384,129] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r9101 c9101
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9101_9
  · exact m9101_33
  · exact m9101_40
  · exact m9101_65
  · exact m9101_72
  · exact m9101_96
  · exact u7676
  · exact u7677
  · exact u7678
  · exact u7679

theorem m9102_9 : Upper (D 9) (R 9) [34,68,384,144,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7650

theorem m9102_33 : Upper (D 9) (R 9) [34,68,384,144,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7657

theorem m9102_40 : Upper (D 9) (R 9) [34,68,384,144,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7662

theorem m9102_65 : Upper (D 9) (R 9) [34,68,384,144,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7666

theorem m9102_72 : Upper (D 9) (R 9) [34,68,384,144,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7670

theorem m9102_96 : Upper (D 9) (R 9) [34,68,384,144,96] 13 :=
  permutation_upper _ _ _ [34,68,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7674

theorem m9102_257 : Upper (D 9) (R 9) [34,68,384,144,257] 13 :=
  permutation_upper _ _ _ [34,68,384,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7677

def r9102 : Route 9 := (fun mask => (mask,id))

def c9102 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9102 : Upper (D 9) (R 9) [34,68,384,144] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r9102 c9102
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9102_9
  · exact m9102_33
  · exact m9102_40
  · exact m9102_65
  · exact m9102_72
  · exact m9102_96
  · exact m9102_257
  · exact u7680
  · exact u7681
  · exact u7682

theorem m9103_9 : Upper (D 9) (R 9) [34,68,384,160,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7651

theorem m9103_65 : Upper (D 9) (R 9) [34,68,384,160,65] 13 :=
  permutation_upper _ _ _ [34,68,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7667

theorem m9103_72 : Upper (D 9) (R 9) [34,68,384,160,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7671

theorem m9103_257 : Upper (D 9) (R 9) [34,68,384,160,257] 13 :=
  permutation_upper _ _ _ [34,68,384,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7678

theorem m9103_264 : Upper (D 9) (R 9) [34,68,384,160,264] 13 :=
  permutation_upper _ _ _ [34,68,384,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7681

def r9103 : Route 9 := (fun mask => (mask,id))

def c9103 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9103 : Upper (D 9) (R 9) [34,68,384,160] 13 := by
  apply FastRouting.sound _ _ [34,68,384,160] 13 (by decide) (choices 2) [9,65,72,257,264,320] r9103 c9103
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9103_9
  · exact m9103_65
  · exact m9103_72
  · exact m9103_257
  · exact m9103_264
  · exact u7683

theorem m9104_9 : Upper (D 9) (R 9) [34,68,384,192,9] 13 :=
  permutation_upper _ _ _ [34,68,384,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7652

theorem m9104_33 : Upper (D 9) (R 9) [34,68,384,192,33] 13 :=
  permutation_upper _ _ _ [34,68,384,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7658

theorem m9104_40 : Upper (D 9) (R 9) [34,68,384,192,40] 13 :=
  permutation_upper _ _ _ [34,68,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7663

theorem m9104_257 : Upper (D 9) (R 9) [34,68,384,192,257] 13 :=
  permutation_upper _ _ _ [34,68,384,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7679

theorem m9104_264 : Upper (D 9) (R 9) [34,68,384,192,264] 13 :=
  permutation_upper _ _ _ [34,68,384,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7682

theorem m9104_288 : Upper (D 9) (R 9) [34,68,384,192,288] 13 :=
  permutation_upper _ _ _ [34,68,384,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7683

def r9104 : Route 9 := (fun mask => (mask,id))

def c9104 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9104 : Upper (D 9) (R 9) [34,68,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,384,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r9104 c9104
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9104_9
  · exact m9104_33
  · exact m9104_40
  · exact m9104_257
  · exact m9104_264
  · exact m9104_288

def b9105 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 97 },{ cop := 3, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5),(3,6)], upper := (rows 35 70 388 392 121 121 121 249 377), lower := (rows 35 70 388 392 16 32 64 128 256), losses := [] }

theorem u9105 : Upper (D 9) (R 9) [34,68,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9105 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9106 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 12, targets := 480 }], pairs := [(2,5),(2,6),(2,7),(2,8),(3,5)], upper := (rows 35 194 13 13 496 496 496 496 496), lower := (rows 35 194 13 13 16 32 64 128 256), losses := [] }

theorem u9106 : Upper (D 9) (R 9) [34,192,9,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9106 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9107 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 4, targets := 480 },{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7),(2,8)], upper := (rows 35 194 13 25 500 484 484 484 484), lower := (rows 35 194 13 25 16 32 64 128 256), losses := [] }

theorem u9107 : Upper (D 9) (R 9) [34,192,9,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9107 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r9108 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9108 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9108 : Upper (D 9) (R 9) [34,192,9,20] 13 := by
  apply FastRouting.sound _ _ [34,192,9,20] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r9108 c9108
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7693
  · exact u7694
  · exact u7695
  · exact u7696
  · exact u7697
  · exact u7698
  · exact u7699

def b9109 : PairBound 9 := { available := 468, camps := [{ cop := 0, region := 12, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 194 13 41 468 500 468 468 468), lower := (rows 35 194 13 41 16 32 64 128 256), losses := [] }

theorem u9109 : Upper (D 9) (R 9) [34,192,9,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9109 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9110 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 12, targets := 448 }], pairs := [(2,6),(2,7),(2,8),(3,6),(3,7)], upper := (rows 35 194 13 44 465 497 465 465 465), lower := (rows 35 194 13 44 16 32 64 128 256), losses := [] }

theorem u9110 : Upper (D 9) (R 9) [34,192,9,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9110 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9111_5 : Upper (D 9) (R 9) [34,192,9,48,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7687

def r9111 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9111 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9111 : Upper (D 9) (R 9) [34,192,9,48] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48] 13 (by decide) (choices 2) [5,65,68,192,257,260,320] r9111 c9111
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9111_5
  · exact u7706
  · exact u7707
  · exact u7708
  · exact u7709
  · exact u7710
  · exact u7711

def b9112 : PairBound 9 := { available := 436, camps := [{ cop := 3, region := 4, targets := 416 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(4,0)], upper := (rows 35 194 13 73 436 436 500 436 436), lower := (rows 35 194 13 73 16 32 64 128 256), losses := [] }

theorem u9112 : Upper (D 9) (R 9) [34,192,9,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9112 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r9113 : Route 9 := (fun mask => (mask,id))

def c9113 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9113 : Upper (D 9) (R 9) [34,192,9,68] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68] 13 (by decide) (choices 2) [33,129,160,257,288,384] r9113 c9113
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7718
  · exact u7719
  · exact u7720
  · exact u7721
  · exact u7722
  · exact u7723

theorem m9114_5 : Upper (D 9) (R 9) [34,192,9,80,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7688

def r9114 : Route 9 := (fun mask => (mask,id))

def c9114 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9114 : Upper (D 9) (R 9) [34,192,9,80] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r9114 c9114
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9114_5
  · exact u7724
  · exact u7725
  · exact u7726
  · exact u7727
  · exact u7728
  · exact u7729
  · exact u7730
  · exact u7731
  · exact u7732

theorem m9115_5 : Upper (D 9) (R 9) [34,192,9,96,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7689

def r9115 : Route 9 := (fun mask => (mask,id))

def c9115 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9115 : Upper (D 9) (R 9) [34,192,9,96] 13 := by
  apply FastRouting.sound _ _ [34,192,9,96] 13 (by decide) (choices 2) [5,129,132,257,260,384] r9115 c9115
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9115_5
  · exact u7733
  · exact u7734
  · exact u7735
  · exact u7736
  · exact u7737

def b9116 : PairBound 9 := { available := 309, camps := [{ cop := 1, region := 8, targets := 289 },{ cop := 3, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5),(3,8)], upper := (rows 35 194 13 200 309 309 373 437 309), lower := (rows 35 194 13 200 16 32 64 128 256), losses := [] }

theorem u9116 : Upper (D 9) (R 9) [34,192,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9116 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9117 : PairBound 9 := { available := 500, camps := [{ cop := 3, region := 4, targets := 480 },{ cop := 2, region := 498, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7),(2,8)], upper := (rows 35 194 13 265 500 500 500 500 500), lower := (rows 35 194 13 265 16 32 64 128 256), losses := [] }

theorem u9117 : Upper (D 9) (R 9) [34,192,9,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9117 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r9118 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9118 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9118 : Upper (D 9) (R 9) [34,192,9,260] 13 := by
  apply FastRouting.sound _ _ [34,192,9,260] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r9118 c9118
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7748
  · exact u7749
  · exact u7750
  · exact u7751
  · exact u7752
  · exact u7753
  · exact u7754

theorem m9119_5 : Upper (D 9) (R 9) [34,192,9,272,5] 13 :=
  permutation_upper _ _ _ [34,192,9,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7690

def r9119 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9119 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9119 : Upper (D 9) (R 9) [34,192,9,272] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272] 13 (by decide) (choices 2) [5,33,36,65,68,96,192,257,260,288,320] r9119 c9119
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9119_5
  · exact u7755
  · exact u7756
  · exact u7757
  · exact u7758
  · exact u7759
  · exact u7760
  · exact u7761
  · exact u7762
  · exact u7763
  · exact u7764

#print axioms u9119
end Delivery.IrregularNine14.P09
