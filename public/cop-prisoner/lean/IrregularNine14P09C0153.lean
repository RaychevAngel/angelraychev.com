import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0128
import IrregularNine14P09C0129
import IrregularNine14P09C0130
import IrregularNine14P09C0131
import IrregularNine14P09C0132
import IrregularNine14P09C0133
import IrregularNine14P09C0134

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m9180_5 : Upper (D 9) (R 9) [34,192,96,257,5] 13 :=
  permutation_upper _ _ _ [34,192,9,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7735

theorem m9180_9 : Upper (D 9) (R 9) [34,192,96,257,9] 13 :=
  permutation_upper _ _ _ [34,192,9,257,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7744

theorem m9180_12 : Upper (D 9) (R 9) [34,192,96,257,12] 13 :=
  permutation_upper _ _ _ [34,192,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7800

theorem m9180_129 : Upper (D 9) (R 9) [34,192,96,257,129] 13 :=
  permutation_upper _ _ _ [34,192,65,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7876

theorem m9180_132 : Upper (D 9) (R 9) [34,192,96,257,132] 13 :=
  permutation_upper _ _ _ [34,192,72,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7895

theorem m9180_136 : Upper (D 9) (R 9) [34,192,96,257,136] 13 :=
  permutation_upper _ _ _ [34,192,72,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7897

def r9180 : Route 9 := (fun mask => (mask,id))

def c9180 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9180 : Upper (D 9) (R 9) [34,192,96,257] 13 := by
  apply FastRouting.sound _ _ [34,192,96,257] 13 (by decide) (choices 2) [5,9,12,129,132,136,257,260,264,384] r9180 c9180
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9180_5
  · exact m9180_9
  · exact m9180_12
  · exact m9180_129
  · exact m9180_132
  · exact m9180_136
  · exact u7917
  · exact u7918
  · exact u7919
  · exact u7920

theorem m9181_9 : Upper (D 9) (R 9) [34,192,96,260,9] 13 :=
  permutation_upper _ _ _ [34,192,9,272,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7759

theorem m9181_129 : Upper (D 9) (R 9) [34,192,96,260,129] 13 :=
  permutation_upper _ _ _ [34,192,65,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7878

theorem m9181_136 : Upper (D 9) (R 9) [34,192,96,260,136] 13 :=
  permutation_upper _ _ _ [34,192,72,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7906

theorem m9181_257 : Upper (D 9) (R 9) [34,192,96,260,257] 13 :=
  permutation_upper _ _ _ [34,192,96,257,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7918

def r9181 : Route 9 := (fun mask => (mask,id))

def c9181 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9181 : Upper (D 9) (R 9) [34,192,96,260] 13 := by
  apply FastRouting.sound _ _ [34,192,96,260] 13 (by decide) (choices 2) [9,129,136,257,264,384] r9181 c9181
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9181_9
  · exact m9181_129
  · exact m9181_136
  · exact m9181_257
  · exact u7921
  · exact u7922

theorem m9182_5 : Upper (D 9) (R 9) [34,192,96,272,5] 13 :=
  permutation_upper _ _ _ [34,192,9,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7736

theorem m9182_9 : Upper (D 9) (R 9) [34,192,96,272,9] 13 :=
  permutation_upper _ _ _ [34,192,9,260,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7750

theorem m9182_12 : Upper (D 9) (R 9) [34,192,96,272,12] 13 :=
  permutation_upper _ _ _ [34,192,24,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7801

theorem m9182_129 : Upper (D 9) (R 9) [34,192,96,272,129] 13 :=
  permutation_upper _ _ _ [34,192,65,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7877

theorem m9182_132 : Upper (D 9) (R 9) [34,192,96,272,132] 13 :=
  permutation_upper _ _ _ [34,192,72,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7896

theorem m9182_136 : Upper (D 9) (R 9) [34,192,96,272,136] 13 :=
  permutation_upper _ _ _ [34,192,72,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7902

theorem m9182_257 : Upper (D 9) (R 9) [34,192,96,272,257] 13 :=
  permutation_upper _ _ _ [34,192,96,257,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7919

theorem m9182_260 : Upper (D 9) (R 9) [34,192,96,272,260] 13 :=
  permutation_upper _ _ _ [34,192,96,260,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7921

def r9182 : Route 9 := (fun mask => (mask,id))

def c9182 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9182 : Upper (D 9) (R 9) [34,192,96,272] 13 := by
  apply FastRouting.sound _ _ [34,192,96,272] 13 (by decide) (choices 2) [5,9,12,129,132,136,257,260,264,384] r9182 c9182
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9182_5
  · exact m9182_9
  · exact m9182_12
  · exact m9182_129
  · exact m9182_132
  · exact m9182_136
  · exact m9182_257
  · exact m9182_260
  · exact u7923
  · exact u7924

theorem m9183_5 : Upper (D 9) (R 9) [34,192,96,384,5] 13 :=
  permutation_upper _ _ _ [34,192,9,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7737

theorem m9183_9 : Upper (D 9) (R 9) [34,192,96,384,9] 13 :=
  permutation_upper _ _ _ [34,192,9,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7775

theorem m9183_12 : Upper (D 9) (R 9) [34,192,96,384,12] 13 :=
  permutation_upper _ _ _ [34,192,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7802

theorem m9183_257 : Upper (D 9) (R 9) [34,192,96,384,257] 13 :=
  permutation_upper _ _ _ [34,192,96,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7920

theorem m9183_260 : Upper (D 9) (R 9) [34,192,96,384,260] 13 :=
  permutation_upper _ _ _ [34,192,96,260,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7922

theorem m9183_264 : Upper (D 9) (R 9) [34,192,96,384,264] 13 :=
  permutation_upper _ _ _ [34,192,96,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7924

def r9183 : Route 9 := (fun mask => (mask,id))

def c9183 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9183 : Upper (D 9) (R 9) [34,192,96,384] 13 := by
  apply FastRouting.sound _ _ [34,192,96,384] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9183 c9183
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9183_5
  · exact m9183_9
  · exact m9183_12
  · exact m9183_257
  · exact m9183_260
  · exact m9183_264

def b9184 : PairBound 9 := { available := 317, camps := [{ cop := 1, region := 4, targets := 289 },{ cop := 2, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5),(2,8)], upper := (rows 35 194 196 265 317 317 381 445 317), lower := (rows 35 194 196 265 16 32 64 128 256), losses := [] }

theorem u9184 : Upper (D 9) (R 9) [34,192,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9184 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9185 : PairBound 9 := { available := 313, camps := [{ cop := 1, region := 4, targets := 289 },{ cop := 2, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5),(2,8)], upper := (rows 35 194 196 268 313 313 377 441 313), lower := (rows 35 194 196 268 16 32 64 128 256), losses := [] }

theorem u9185 : Upper (D 9) (R 9) [34,192,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9185 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9186 : PairBound 9 := { available := 285, camps := [{ cop := 1, region := 4, targets := 289 },{ cop := 2, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5),(2,8)], upper := (rows 35 194 196 296 285 317 349 413 285), lower := (rows 35 194 196 296 16 32 64 128 256), losses := [] }

theorem u9186 : Upper (D 9) (R 9) [34,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9186 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9187 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 8, targets := 224 },{ cop := 3, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6),(3,7)], upper := (rows 35 194 261 265 252 252 252 252 508), lower := (rows 35 194 261 265 16 32 64 128 256), losses := [] }

theorem u9187 : Upper (D 9) (R 9) [34,192,257,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9187 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9188 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 8, targets := 225 },{ cop := 3, region := 243, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 35 194 261 268 249 249 249 249 505), lower := (rows 35 194 261 268 16 32 64 128 256), losses := [] }

theorem u9188 : Upper (D 9) (R 9) [34,192,257,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9188 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9189_5 : Upper (D 9) (R 9) [34,192,257,272,5] 13 :=
  permutation_upper _ _ _ [34,192,9,257,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7745

theorem m9189_9 : Upper (D 9) (R 9) [34,192,257,272,9] 13 :=
  permutation_upper _ _ _ [34,192,9,260,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7752

theorem m9189_12 : Upper (D 9) (R 9) [34,192,257,272,12] 13 :=
  permutation_upper _ _ _ [34,192,24,257,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7807

theorem m9189_33 : Upper (D 9) (R 9) [34,192,257,272,33] 13 :=
  permutation_upper _ _ _ [34,192,33,257,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7827

theorem m9189_36 : Upper (D 9) (R 9) [34,192,257,272,36] 13 :=
  permutation_upper _ _ _ [34,192,40,257,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7850

theorem m9189_40 : Upper (D 9) (R 9) [34,192,257,272,40] 13 :=
  permutation_upper _ _ _ [34,192,40,260,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7854

theorem m9189_65 : Upper (D 9) (R 9) [34,192,257,272,65] 13 :=
  permutation_upper _ _ _ [34,192,65,257,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7879

theorem m9189_68 : Upper (D 9) (R 9) [34,192,257,272,68] 13 :=
  permutation_upper _ _ _ [34,192,72,257,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7899

theorem m9189_72 : Upper (D 9) (R 9) [34,192,257,272,72] 13 :=
  permutation_upper _ _ _ [34,192,72,260,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7903

theorem m9189_96 : Upper (D 9) (R 9) [34,192,257,272,96] 13 :=
  permutation_upper _ _ _ [34,192,96,257,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7918

theorem m9189_192 : Upper (D 9) (R 9) [34,192,257,272,192] 13 :=
  permutation_upper _ _ _ [34,192,192,257,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7925

def r9189 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9189 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9189 : Upper (D 9) (R 9) [34,192,257,272] 13 := by
  apply FastRouting.sound _ _ [34,192,257,272] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,192] r9189 c9189
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9189_5
  · exact m9189_9
  · exact m9189_12
  · exact m9189_33
  · exact m9189_36
  · exact m9189_40
  · exact m9189_65
  · exact m9189_68
  · exact m9189_72
  · exact m9189_96
  · exact m9189_192

theorem m9190_5 : Upper (D 9) (R 9) [34,192,257,288,5] 13 :=
  permutation_upper _ _ _ [34,192,9,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7746

theorem m9190_9 : Upper (D 9) (R 9) [34,192,257,288,9] 13 :=
  permutation_upper _ _ _ [34,192,9,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7768

theorem m9190_12 : Upper (D 9) (R 9) [34,192,257,288,12] 13 :=
  permutation_upper _ _ _ [34,192,24,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7808

theorem m9190_65 : Upper (D 9) (R 9) [34,192,257,288,65] 13 :=
  permutation_upper _ _ _ [34,192,65,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7881

theorem m9190_68 : Upper (D 9) (R 9) [34,192,257,288,68] 13 :=
  permutation_upper _ _ _ [34,192,72,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7900

theorem m9190_72 : Upper (D 9) (R 9) [34,192,257,288,72] 13 :=
  permutation_upper _ _ _ [34,192,72,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7911

theorem m9190_192 : Upper (D 9) (R 9) [34,192,257,288,192] 13 :=
  permutation_upper _ _ _ [34,192,192,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7926

def r9190 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9190 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9190 : Upper (D 9) (R 9) [34,192,257,288] 13 := by
  apply FastRouting.sound _ _ [34,192,257,288] 13 (by decide) (choices 2) [5,9,12,65,68,72,192] r9190 c9190
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9190_5
  · exact m9190_9
  · exact m9190_12
  · exact m9190_65
  · exact m9190_68
  · exact m9190_72
  · exact m9190_192

theorem m9191_5 : Upper (D 9) (R 9) [34,192,257,320,5] 13 :=
  permutation_upper _ _ _ [34,192,9,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7747

theorem m9191_9 : Upper (D 9) (R 9) [34,192,257,320,9] 13 :=
  permutation_upper _ _ _ [34,192,9,320,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7776

theorem m9191_12 : Upper (D 9) (R 9) [34,192,257,320,12] 13 :=
  permutation_upper _ _ _ [34,192,24,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7809

theorem m9191_33 : Upper (D 9) (R 9) [34,192,257,320,33] 13 :=
  permutation_upper _ _ _ [34,192,33,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7828

theorem m9191_36 : Upper (D 9) (R 9) [34,192,257,320,36] 13 :=
  permutation_upper _ _ _ [34,192,40,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7851

theorem m9191_40 : Upper (D 9) (R 9) [34,192,257,320,40] 13 :=
  permutation_upper _ _ _ [34,192,40,320,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7864

theorem m9191_129 : Upper (D 9) (R 9) [34,192,257,320,129] 13 :=
  permutation_upper _ _ _ [34,192,65,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7882

theorem m9191_132 : Upper (D 9) (R 9) [34,192,257,320,132] 13 :=
  permutation_upper _ _ _ [34,192,72,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7901

theorem m9191_136 : Upper (D 9) (R 9) [34,192,257,320,136] 13 :=
  permutation_upper _ _ _ [34,192,72,384,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7914

theorem m9191_160 : Upper (D 9) (R 9) [34,192,257,320,160] 13 :=
  permutation_upper _ _ _ [34,192,96,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7920

def r9191 : Route 9 := (fun mask => (mask,id))

def c9191 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9191 : Upper (D 9) (R 9) [34,192,257,320] 13 := by
  apply FastRouting.sound _ _ [34,192,257,320] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r9191 c9191
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9191_5
  · exact m9191_9
  · exact m9191_12
  · exact m9191_33
  · exact m9191_36
  · exact m9191_40
  · exact m9191_129
  · exact m9191_132
  · exact m9191_136
  · exact m9191_160

def b9192 : PairBound 9 := { available := 241, camps := [{ cop := 8, region := 12, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7),(3,0)], upper := (rows 35 194 268 268 241 241 241 241 497), lower := (rows 35 194 268 268 16 32 64 128 256), losses := [] }

theorem u9192 : Upper (D 9) (R 9) [34,192,264,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9192 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9193 : PairBound 9 := { available := 229, camps := [{ cop := 3, region := 4, targets := 225 },{ cop := 2, region := 227, targets := 256 }], pairs := [(0,8),(2,0),(2,5),(2,6),(2,7)], upper := (rows 35 194 268 280 245 229 229 229 485), lower := (rows 35 194 268 280 16 32 64 128 256), losses := [] }

theorem u9193 : Upper (D 9) (R 9) [34,192,264,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9193 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9194 : PairBound 9 := { available := 213, camps := [{ cop := 3, region := 4, targets := 225 },{ cop := 2, region := 243, targets := 256 }], pairs := [(0,8),(2,0),(2,5),(2,6),(2,7)], upper := (rows 35 194 268 296 213 245 213 213 469), lower := (rows 35 194 268 296 16 32 64 128 256), losses := [] }

theorem u9194 : Upper (D 9) (R 9) [34,192,264,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9194 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9195 : PairBound 9 := { available := 181, camps := [{ cop := 3, region := 4, targets := 225 },{ cop := 2, region := 243, targets := 256 }], pairs := [(0,8),(2,0),(2,5),(2,6),(2,7)], upper := (rows 35 194 268 328 181 181 245 181 437), lower := (rows 35 194 268 328 16 32 64 128 256), losses := [] }

theorem u9195 : Upper (D 9) (R 9) [34,192,264,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9195 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9196_5 : Upper (D 9) (R 9) [34,192,272,288,5] 13 :=
  permutation_upper _ _ _ [34,192,9,260,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7753

theorem m9196_9 : Upper (D 9) (R 9) [34,192,272,288,9] 13 :=
  permutation_upper _ _ _ [34,192,9,288,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7769

theorem m9196_12 : Upper (D 9) (R 9) [34,192,272,288,12] 13 :=
  permutation_upper _ _ _ [34,192,24,260,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7810

theorem m9196_65 : Upper (D 9) (R 9) [34,192,272,288,65] 13 :=
  permutation_upper _ _ _ [34,192,65,260,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7884

theorem m9196_68 : Upper (D 9) (R 9) [34,192,272,288,68] 13 :=
  permutation_upper _ _ _ [34,192,72,260,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7904

theorem m9196_72 : Upper (D 9) (R 9) [34,192,272,288,72] 13 :=
  permutation_upper _ _ _ [34,192,72,288,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7912

theorem m9196_192 : Upper (D 9) (R 9) [34,192,272,288,192] 13 :=
  permutation_upper _ _ _ [34,192,192,260,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7927

def r9196 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9196 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9196 : Upper (D 9) (R 9) [34,192,272,288] 13 := by
  apply FastRouting.sound _ _ [34,192,272,288] 13 (by decide) (choices 2) [5,9,12,65,68,72,192] r9196 c9196
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9196_5
  · exact m9196_9
  · exact m9196_12
  · exact m9196_65
  · exact m9196_68
  · exact m9196_72
  · exact m9196_192

theorem m9197_5 : Upper (D 9) (R 9) [34,192,272,320,5] 13 :=
  permutation_upper _ _ _ [34,192,9,260,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7754

theorem m9197_9 : Upper (D 9) (R 9) [34,192,272,320,9] 13 :=
  permutation_upper _ _ _ [34,192,9,320,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7777

theorem m9197_12 : Upper (D 9) (R 9) [34,192,272,320,12] 13 :=
  permutation_upper _ _ _ [34,192,24,260,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7811

theorem m9197_33 : Upper (D 9) (R 9) [34,192,272,320,33] 13 :=
  permutation_upper _ _ _ [34,192,33,260,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7829

theorem m9197_36 : Upper (D 9) (R 9) [34,192,272,320,36] 13 :=
  permutation_upper _ _ _ [34,192,40,260,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7855

theorem m9197_40 : Upper (D 9) (R 9) [34,192,272,320,40] 13 :=
  permutation_upper _ _ _ [34,192,40,320,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7865

theorem m9197_129 : Upper (D 9) (R 9) [34,192,272,320,129] 13 :=
  permutation_upper _ _ _ [34,192,65,260,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7885

theorem m9197_132 : Upper (D 9) (R 9) [34,192,272,320,132] 13 :=
  permutation_upper _ _ _ [34,192,72,260,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7905

theorem m9197_136 : Upper (D 9) (R 9) [34,192,272,320,136] 13 :=
  permutation_upper _ _ _ [34,192,72,384,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7915

theorem m9197_160 : Upper (D 9) (R 9) [34,192,272,320,160] 13 :=
  permutation_upper _ _ _ [34,192,96,260,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7922

def r9197 : Route 9 := (fun mask => (mask,id))

def c9197 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9197 : Upper (D 9) (R 9) [34,192,272,320] 13 := by
  apply FastRouting.sound _ _ [34,192,272,320] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r9197 c9197
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9197_5
  · exact m9197_9
  · exact m9197_12
  · exact m9197_33
  · exact m9197_36
  · exact m9197_40
  · exact m9197_129
  · exact m9197_132
  · exact m9197_136
  · exact m9197_160

theorem m9198_5 : Upper (D 9) (R 9) [34,192,288,320,5] 13 :=
  permutation_upper _ _ _ [34,192,9,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7770

theorem m9198_9 : Upper (D 9) (R 9) [34,192,288,320,9] 13 :=
  permutation_upper _ _ _ [34,192,9,320,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7778

theorem m9198_12 : Upper (D 9) (R 9) [34,192,288,320,12] 13 :=
  permutation_upper _ _ _ [34,192,24,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7812

theorem m9198_129 : Upper (D 9) (R 9) [34,192,288,320,129] 13 :=
  permutation_upper _ _ _ [34,192,65,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7889

theorem m9198_132 : Upper (D 9) (R 9) [34,192,288,320,132] 13 :=
  permutation_upper _ _ _ [34,192,72,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7913

theorem m9198_136 : Upper (D 9) (R 9) [34,192,288,320,136] 13 :=
  permutation_upper _ _ _ [34,192,72,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7916

def r9198 : Route 9 := (fun mask => (mask,id))

def c9198 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9198 : Upper (D 9) (R 9) [34,192,288,320] 13 := by
  apply FastRouting.sound _ _ [34,192,288,320] 13 (by decide) (choices 2) [5,9,12,129,132,136] r9198 c9198
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9198_5
  · exact m9198_9
  · exact m9198_12
  · exact m9198_129
  · exact m9198_132
  · exact m9198_136

theorem m9199_5 : Upper (D 9) (R 9) [34,192,320,384,5] 13 :=
  permutation_upper _ _ _ [34,192,9,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7779

theorem m9199_9 : Upper (D 9) (R 9) [34,192,320,384,9] 13 :=
  permutation_upper _ _ _ [34,192,9,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7779

theorem m9199_12 : Upper (D 9) (R 9) [34,192,320,384,12] 13 :=
  permutation_upper _ _ _ [34,192,24,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7813

theorem m9199_33 : Upper (D 9) (R 9) [34,192,320,384,33] 13 :=
  permutation_upper _ _ _ [34,192,33,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7830

theorem m9199_36 : Upper (D 9) (R 9) [34,192,320,384,36] 13 :=
  permutation_upper _ _ _ [34,192,40,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7866

theorem m9199_40 : Upper (D 9) (R 9) [34,192,320,384,40] 13 :=
  permutation_upper _ _ _ [34,192,40,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7866

def r9199 : Route 9 := (fun mask => (mask,id))

def c9199 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9199 : Upper (D 9) (R 9) [34,192,320,384] 13 := by
  apply FastRouting.sound _ _ [34,192,320,384] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9199 c9199
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9199_5
  · exact m9199_9
  · exact m9199_12
  · exact m9199_33
  · exact m9199_36
  · exact m9199_40

def b9200 : PairBound 9 := { available := 472, camps := [{ cop := 0, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 7 168 472 504 472 472 472), lower := (rows 97 7 7 168 16 32 64 128 256), losses := [] }

theorem u9200 : Upper (D 9) (R 9) [96,5,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9200 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9201 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 7 392 504 504 504 504 504), lower := (rows 97 7 7 392 16 32 64 128 256), losses := [] }

theorem u9201 : Upper (D 9) (R 9) [96,5,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9201 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9202 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 13 26 496 480 480 480 480), lower := (rows 97 7 13 26 16 32 64 128 256), losses := [] }

theorem u9202 : Upper (D 9) (R 9) [96,5,9,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9202 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9203 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 14, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 13 42 464 496 464 464 464), lower := (rows 97 7 13 42 16 32 64 128 256), losses := [] }

theorem u9203 : Upper (D 9) (R 9) [96,5,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9203 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9204 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 13 138 496 496 496 496 496), lower := (rows 97 7 13 138 16 32 64 128 256), losses := [] }

theorem u9204 : Upper (D 9) (R 9) [96,5,9,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9204 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9205 : PairBound 9 := { available := 466, camps := [{ cop := 2, region := 2, targets := 448 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,6),(1,7),(1,8),(3,0),(4,0)], upper := (rows 97 7 13 168 466 498 466 466 466), lower := (rows 97 7 13 168 16 32 64 128 256), losses := [] }

theorem u9205 : Upper (D 9) (R 9) [96,5,9,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9205 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9206 : PairBound 9 := { available := 498, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 504, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 13 392 498 498 498 498 498), lower := (rows 97 7 13 392 16 32 64 128 256), losses := [] }

theorem u9206 : Upper (D 9) (R 9) [96,5,9,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9206 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9207 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 14 25 496 480 480 480 480), lower := (rows 97 7 14 25 16 32 64 128 256), losses := [] }

theorem u9207 : Upper (D 9) (R 9) [96,5,10,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9207 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9208 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 14, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 14 41 464 496 464 464 464), lower := (rows 97 7 14 41 16 32 64 128 256), losses := [] }

theorem u9208 : Upper (D 9) (R 9) [96,5,10,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9208 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r9209 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9209 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9209 : Upper (D 9) (R 9) [96,5,10,48] 13 := by
  apply FastRouting.sound _ _ [96,5,10,48] 13 (by decide) (choices 2) [65,129,192,384] r9209 c9209
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7963
  · exact u7964
  · exact u7965
  · exact u7966

def b9210 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 14 104 401 433 465 401 401), lower := (rows 97 7 14 104 16 32 64 128 256), losses := [] }

theorem u9210 : Upper (D 9) (R 9) [96,5,10,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9210 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9211 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 6, targets := 480 }], pairs := [(1,5),(1,6),(1,7),(1,8),(2,5)], upper := (rows 97 7 14 137 496 496 496 496 496), lower := (rows 97 7 14 137 16 32 64 128 256), losses := [] }

theorem u9211 : Upper (D 9) (R 9) [96,5,10,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9211 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r9212 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9212 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9212 : Upper (D 9) (R 9) [96,5,10,144] 13 := by
  apply FastRouting.sound _ _ [96,5,10,144] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r9212 c9212
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7972
  · exact u7973
  · exact u7974
  · exact u7975
  · exact u7976
  · exact u7977
  · exact u7978

def r9213 : Route 9 := (fun mask => (mask,id))

def c9213 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9213 : Upper (D 9) (R 9) [96,5,10,160] 13 := by
  apply FastRouting.sound _ _ [96,5,10,160] 13 (by decide) (choices 2) [65,129,192,257,320,384] r9213 c9213
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7979
  · exact u7980
  · exact u7981
  · exact u7982
  · exact u7983
  · exact u7984

def r9214 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9214 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9214 : Upper (D 9) (R 9) [96,5,10,384] 13 := by
  apply FastRouting.sound _ _ [96,5,10,384] 13 (by decide) (choices 2) [33,96,129,160,384] r9214 c9214
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u7985
  · exact u7986
  · exact u7987
  · exact u7988
  · exact u7989

def b9215 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 488, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 21 42 472 488 456 456 456), lower := (rows 97 7 21 42 16 32 64 128 256), losses := [] }

theorem u9215 : Upper (D 9) (R 9) [96,5,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9215 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9216 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 488, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 21 138 504 488 488 488 488), lower := (rows 97 7 21 138 16 32 64 128 256), losses := [] }

theorem u9216 : Upper (D 9) (R 9) [96,5,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9216 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9217 : PairBound 9 := { available := 458, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 488, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 21 168 474 490 458 458 458), lower := (rows 97 7 21 168 16 32 64 128 256), losses := [] }

theorem u9217 : Upper (D 9) (R 9) [96,5,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9217 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9218 : PairBound 9 := { available := 490, camps := [{ cop := 2, region := 2, targets := 480 },{ cop := 1, region := 488, targets := 1 }], pairs := [(1,5),(1,6),(1,7),(1,8),(3,0)], upper := (rows 97 7 21 392 506 490 490 490 490), lower := (rows 97 7 21 392 16 32 64 128 256), losses := [] }

theorem u9218 : Upper (D 9) (R 9) [96,5,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9218 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9219_40 : Upper (D 9) (R 9) [96,5,18,129,40] 13 :=
  permutation_upper _ _ _ [96,5,10,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7964

theorem m9219_96 : Upper (D 9) (R 9) [96,5,18,129,96] 13 :=
  permutation_upper _ _ _ [96,5,10,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7967

theorem m9219_136 : Upper (D 9) (R 9) [96,5,18,129,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7974

theorem m9219_160 : Upper (D 9) (R 9) [96,5,18,129,160] 13 :=
  permutation_upper _ _ _ [96,5,10,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7980

theorem m9219_264 : Upper (D 9) (R 9) [96,5,18,129,264] 13 :=
  permutation_upper _ _ _ [96,5,10,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7976

theorem m9219_288 : Upper (D 9) (R 9) [96,5,18,129,288] 13 :=
  permutation_upper _ _ _ [96,5,10,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7982

theorem m9219_384 : Upper (D 9) (R 9) [96,5,18,129,384] 13 :=
  permutation_upper _ _ _ [96,5,10,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7987

def r9219 : Route 9 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9219 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9219 : Upper (D 9) (R 9) [96,5,18,129] 13 := by
  apply FastRouting.sound _ _ [96,5,18,129] 13 (by decide) (choices 2) [40,96,136,160,264,288,384] r9219 c9219
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9219_40
  · exact m9219_96
  · exact m9219_136
  · exact m9219_160
  · exact m9219_264
  · exact m9219_288
  · exact m9219_384

theorem m9220_9 : Upper (D 9) (R 9) [96,5,18,160,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7959

theorem m9220_65 : Upper (D 9) (R 9) [96,5,18,160,65] 13 :=
  permutation_upper _ _ _ [96,5,10,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7961

theorem m9220_72 : Upper (D 9) (R 9) [96,5,18,160,72] 13 :=
  permutation_upper _ _ _ [96,5,10,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7965

theorem m9220_129 : Upper (D 9) (R 9) [96,5,18,160,129] 13 :=
  permutation_upper _ _ _ [96,5,10,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7969

theorem m9220_136 : Upper (D 9) (R 9) [96,5,18,160,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7975

theorem m9220_192 : Upper (D 9) (R 9) [96,5,18,160,192] 13 :=
  permutation_upper _ _ _ [96,5,10,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7981

theorem m9220_257 : Upper (D 9) (R 9) [96,5,18,160,257] 13 :=
  permutation_upper _ _ _ [96,5,10,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7970

theorem m9220_264 : Upper (D 9) (R 9) [96,5,18,160,264] 13 :=
  permutation_upper _ _ _ [96,5,10,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7977

theorem m9220_320 : Upper (D 9) (R 9) [96,5,18,160,320] 13 :=
  permutation_upper _ _ _ [96,5,10,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7983

theorem m9220_384 : Upper (D 9) (R 9) [96,5,18,160,384] 13 :=
  permutation_upper _ _ _ [96,5,10,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7988

def r9220 : Route 9 := (fun mask => (mask,id))

def c9220 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9220 : Upper (D 9) (R 9) [96,5,18,160] 13 := by
  apply FastRouting.sound _ _ [96,5,18,160] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r9220 c9220
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9220_9
  · exact m9220_65
  · exact m9220_72
  · exact m9220_129
  · exact m9220_136
  · exact m9220_192
  · exact m9220_257
  · exact m9220_264
  · exact m9220_320
  · exact m9220_384

theorem m9221_9 : Upper (D 9) (R 9) [96,5,18,384,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7960

theorem m9221_33 : Upper (D 9) (R 9) [96,5,18,384,33] 13 :=
  permutation_upper _ _ _ [96,5,10,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7962

theorem m9221_40 : Upper (D 9) (R 9) [96,5,18,384,40] 13 :=
  permutation_upper _ _ _ [96,5,10,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7966

theorem m9221_96 : Upper (D 9) (R 9) [96,5,18,384,96] 13 :=
  permutation_upper _ _ _ [96,5,10,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7968

theorem m9221_129 : Upper (D 9) (R 9) [96,5,18,384,129] 13 :=
  permutation_upper _ _ _ [96,5,10,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7971

theorem m9221_136 : Upper (D 9) (R 9) [96,5,18,384,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7978

theorem m9221_160 : Upper (D 9) (R 9) [96,5,18,384,160] 13 :=
  permutation_upper _ _ _ [96,5,10,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7984

theorem m9221_384 : Upper (D 9) (R 9) [96,5,18,384,384] 13 :=
  permutation_upper _ _ _ [96,5,10,384,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7989

def r9221 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9221 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9221 : Upper (D 9) (R 9) [96,5,18,384] 13 := by
  apply FastRouting.sound _ _ [96,5,18,384] 13 (by decide) (choices 2) [9,33,40,96,129,136,160,384] r9221 c9221
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9221_9
  · exact m9221_33
  · exact m9221_40
  · exact m9221_96
  · exact m9221_129
  · exact m9221_136
  · exact m9221_160
  · exact m9221_384

def b9222 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 8, targets := 448 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(3,7),(3,8)], upper := (rows 97 7 28 41 466 482 450 450 450), lower := (rows 97 7 28 41 16 32 64 128 256), losses := [] }

theorem u9222 : Upper (D 9) (R 9) [96,5,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9222 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9223_65 : Upper (D 9) (R 9) [96,5,24,34,65] 13 :=
  permutation_upper _ _ _ [96,5,24,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7990

def r9223 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9223 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9223 : Upper (D 9) (R 9) [96,5,24,34] 13 := by
  apply FastRouting.sound _ _ [96,5,24,34] 13 (by decide) (choices 2) [65,129,192,384] r9223 c9223
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m9223_65
  · exact u7994
  · exact u7995
  · exact u7996

def b9224 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 8, targets := 384 },{ cop := 3, region := 1, targets := 384 },{ cop := 0, region := 8, targets := 1 }], pairs := [(0,7),(0,8),(3,0),(3,7),(3,8)], upper := (rows 97 7 28 104 403 419 451 387 387), lower := (rows 97 7 28 104 16 32 64 128 256), losses := [] }

theorem u9224 : Upper (D 9) (R 9) [96,5,24,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9224 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9225_34 : Upper (D 9) (R 9) [96,5,24,129,34] 13 :=
  permutation_upper _ _ _ [96,5,24,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7994

theorem m9225_96 : Upper (D 9) (R 9) [96,5,24,129,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7997

def r9225 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9225 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9225 : Upper (D 9) (R 9) [96,5,24,129] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129] 13 (by decide) (choices 2) [34,96,130,160,258,288,384] r9225 c9225
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9225_34
  · exact m9225_96
  · exact u8000
  · exact u8001
  · exact u8002
  · exact u8003
  · exact u8004

theorem m9226_33 : Upper (D 9) (R 9) [96,5,24,130,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7991

theorem m9226_96 : Upper (D 9) (R 9) [96,5,24,130,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7998

theorem m9226_129 : Upper (D 9) (R 9) [96,5,24,130,129] 13 :=
  permutation_upper _ _ _ [96,5,24,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8000

theorem m9226_257 : Upper (D 9) (R 9) [96,5,24,130,257] 13 :=
  permutation_upper _ _ _ [96,5,24,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8002

def r9226 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9226 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9226 : Upper (D 9) (R 9) [96,5,24,130] 13 := by
  apply FastRouting.sound _ _ [96,5,24,130] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r9226 c9226
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9226_33
  · exact m9226_96
  · exact m9226_129
  · exact u8005
  · exact m9226_257
  · exact u8006
  · exact u8007

theorem m9227_3 : Upper (D 9) (R 9) [96,5,24,160,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7936

theorem m9227_65 : Upper (D 9) (R 9) [96,5,24,160,65] 13 :=
  permutation_upper _ _ _ [96,5,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7992

theorem m9227_66 : Upper (D 9) (R 9) [96,5,24,160,66] 13 :=
  permutation_upper _ _ _ [96,5,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7995

theorem m9227_129 : Upper (D 9) (R 9) [96,5,24,160,129] 13 :=
  permutation_upper _ _ _ [96,5,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8001

theorem m9227_130 : Upper (D 9) (R 9) [96,5,24,160,130] 13 :=
  permutation_upper _ _ _ [96,5,24,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8005

theorem m9227_257 : Upper (D 9) (R 9) [96,5,24,160,257] 13 :=
  permutation_upper _ _ _ [96,5,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8003

theorem m9227_258 : Upper (D 9) (R 9) [96,5,24,160,258] 13 :=
  permutation_upper _ _ _ [96,5,24,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8006

def r9227 : Route 9 := (fun mask => (mask,id))

def c9227 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9227 : Upper (D 9) (R 9) [96,5,24,160] 13 := by
  apply FastRouting.sound _ _ [96,5,24,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r9227 c9227
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9227_3
  · exact m9227_65
  · exact m9227_66
  · exact m9227_129
  · exact m9227_130
  · exact u8008
  · exact m9227_257
  · exact m9227_258
  · exact u8009
  · exact u8010

theorem m9228_3 : Upper (D 9) (R 9) [96,5,24,384,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7937

theorem m9228_33 : Upper (D 9) (R 9) [96,5,24,384,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7993

theorem m9228_34 : Upper (D 9) (R 9) [96,5,24,384,34] 13 :=
  permutation_upper _ _ _ [96,5,24,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7996

theorem m9228_96 : Upper (D 9) (R 9) [96,5,24,384,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7999

theorem m9228_129 : Upper (D 9) (R 9) [96,5,24,384,129] 13 :=
  permutation_upper _ _ _ [96,5,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8004

theorem m9228_130 : Upper (D 9) (R 9) [96,5,24,384,130] 13 :=
  permutation_upper _ _ _ [96,5,24,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8007

theorem m9228_160 : Upper (D 9) (R 9) [96,5,24,384,160] 13 :=
  permutation_upper _ _ _ [96,5,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8010

def r9228 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9228 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9228 : Upper (D 9) (R 9) [96,5,24,384] 13 := by
  apply FastRouting.sound _ _ [96,5,24,384] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,384] r9228 c9228
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9228_3
  · exact m9228_33
  · exact m9228_34
  · exact m9228_96
  · exact m9228_129
  · exact m9228_130
  · exact m9228_160
  · exact u8011

def b9229 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 26 472 488 456 456 456), lower := (rows 97 7 37 26 16 32 64 128 256), losses := [] }

theorem u9229 : Upper (D 9) (R 9) [96,5,33,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9229 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9230 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 37 74 408 440 472 408 408), lower := (rows 97 7 37 74 16 32 64 128 256), losses := [] }

theorem u9230 : Upper (D 9) (R 9) [96,5,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9230 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9231 : PairBound 9 := { available := 472, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 138 472 504 472 472 472), lower := (rows 97 7 37 138 16 32 64 128 256), losses := [] }

theorem u9231 : Upper (D 9) (R 9) [96,5,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9231 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9232 : PairBound 9 := { available := 410, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 200 410 442 474 410 410), lower := (rows 97 7 37 200 16 32 64 128 256), losses := [] }

theorem u9232 : Upper (D 9) (R 9) [96,5,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9232 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9233 : PairBound 9 := { available := 474, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 37 392 474 506 474 474 474), lower := (rows 97 7 37 392 16 32 64 128 256), losses := [] }

theorem u9233 : Upper (D 9) (R 9) [96,5,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9233 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9234 : PairBound 9 := { available := 472, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 137 472 504 472 472 472), lower := (rows 97 7 38 137 16 32 64 128 256), losses := [] }

theorem u9234 : Upper (D 9) (R 9) [96,5,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9234 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9235 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 200 409 441 473 409 409), lower := (rows 97 7 38 200 16 32 64 128 256), losses := [] }

theorem u9235 : Upper (D 9) (R 9) [96,5,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9235 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9236 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 6, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(2,6),(2,7)], upper := (rows 97 7 38 392 473 505 473 473 473), lower := (rows 97 7 38 392 16 32 64 128 256), losses := [] }

theorem u9236 : Upper (D 9) (R 9) [96,5,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9236 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r9237 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9237 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9237 : Upper (D 9) (R 9) [96,5,40,17] 13 := by
  apply FastRouting.sound _ _ [96,5,40,17] 13 (by decide) (choices 2) [66,130,192,384] r9237 c9237
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8041
  · exact u8042
  · exact u8043
  · exact u8044

def r9238 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9238 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9238 : Upper (D 9) (R 9) [96,5,40,18] 13 := by
  apply FastRouting.sound _ _ [96,5,40,18] 13 (by decide) (choices 2) [65,129,192,384] r9238 c9238
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8045
  · exact u8046
  · exact u8047
  · exact u8048

def b9239 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 14, targets := 384 }], pairs := [(1,7),(1,8),(2,7),(2,8),(3,7)], upper := (rows 97 7 44 73 402 434 466 402 402), lower := (rows 97 7 44 73 16 32 64 128 256), losses := [] }

theorem u9239 : Upper (D 9) (R 9) [96,5,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9239 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u9239
end Delivery.IrregularNine14.P09
