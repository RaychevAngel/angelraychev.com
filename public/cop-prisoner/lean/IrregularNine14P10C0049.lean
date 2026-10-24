import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0018
import IrregularNine14P10C0019
import IrregularNine14P10C0020
import IrregularNine14P10C0021
import IrregularNine14P10C0023
import IrregularNine14P10C0025
import IrregularNine14P10C0027
import IrregularNine14P10C0028
import IrregularNine14P10C0029
import IrregularNine14P10C0030

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2940 : PairBound 9 := { available := 300, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 19 194 69 392 316 300 364 428 300), lower := (rows 19 194 69 392 16 32 64 128 256), losses := [] }

theorem u2940 : Upper (D 10) (R 10) [18,192,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2940 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2941 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 12, targets := 288 }], pairs := [(2,5),(2,8)], upper := (rows 19 194 76 140 305 289 353 417 289), lower := (rows 19 194 76 140 16 32 64 128 256), losses := [] }

theorem u2941 : Upper (D 10) (R 10) [18,192,72,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2941 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2942_5 : Upper (D 10) (R 10) [18,192,72,160,5] 13 :=
  permutation_upper _ _ _ [6,9,80,192,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1129

theorem m2942_33 : Upper (D 10) (R 10) [18,192,72,160,33] 13 :=
  permutation_upper _ _ _ [6,33,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1265

theorem m2942_36 : Upper (D 10) (R 10) [18,192,72,160,36] 13 :=
  permutation_upper _ _ _ [6,40,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1405

theorem m2942_257 : Upper (D 10) (R 10) [18,192,72,160,257] 13 :=
  permutation_upper _ _ _ [6,65,384,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1534

theorem m2942_260 : Upper (D 10) (R 10) [18,192,72,160,260] 13 :=
  permutation_upper _ _ _ [6,72,384,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1717

theorem m2942_288 : Upper (D 10) (R 10) [18,192,72,160,288] 13 :=
  permutation_upper _ _ _ [6,96,384,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1824

def r2942 : Route 9 := (fun mask => (mask,id))

def c2942 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u2942 : Upper (D 10) (R 10) [18,192,72,160] 13 := by
  apply FastRouting.sound _ _ [18,192,72,160] 13 (by decide) (choices 2) [5,33,36,257,260,288] r2942 c2942
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2942_5
  · exact m2942_33
  · exact m2942_36
  · exact m2942_257
  · exact m2942_260
  · exact m2942_288

theorem m2943_36 : Upper (D 10) (R 10) [18,192,72,257,36] 13 :=
  permutation_upper _ _ _ [6,40,192,80,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1406

theorem m2943_132 : Upper (D 10) (R 10) [18,192,72,257,132] 13 :=
  permutation_upper _ _ _ [6,72,192,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1675

theorem m2943_160 : Upper (D 10) (R 10) [18,192,72,257,160] 13 :=
  permutation_upper _ _ _ [6,96,192,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1787

theorem m2943_260 : Upper (D 10) (R 10) [18,192,72,257,260] 13 :=
  permutation_upper _ _ _ [6,72,384,144,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1714

theorem m2943_288 : Upper (D 10) (R 10) [18,192,72,257,288] 13 :=
  permutation_upper _ _ _ [6,96,384,65,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1812

theorem m2943_384 : Upper (D 10) (R 10) [18,192,72,257,384] 13 :=
  permutation_upper _ _ _ [6,192,320,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1839

def r2943 : Route 9 := (fun mask => (mask,id))

def c2943 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2943 : Upper (D 10) (R 10) [18,192,72,257] 13 := by
  apply FastRouting.sound _ _ [18,192,72,257] 13 (by decide) (choices 2) [36,132,160,260,288,384] r2943 c2943
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2943_36
  · exact m2943_132
  · exact m2943_160
  · exact m2943_260
  · exact m2943_288
  · exact m2943_384

def b2944 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 19 194 76 268 433 417 481 417 417), lower := (rows 19 194 76 268 16 32 64 128 256), losses := [] }

theorem u2944 : Upper (D 10) (R 10) [18,192,72,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2944 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2945_5 : Upper (D 10) (R 10) [18,192,72,288,5] 13 :=
  permutation_upper _ _ _ [6,9,80,192,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1130

theorem m2945_33 : Upper (D 10) (R 10) [18,192,72,288,33] 13 :=
  permutation_upper _ _ _ [6,33,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1267

theorem m2945_36 : Upper (D 10) (R 10) [18,192,72,288,36] 13 :=
  permutation_upper _ _ _ [6,40,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1407

theorem m2945_129 : Upper (D 10) (R 10) [18,192,72,288,129] 13 :=
  permutation_upper _ _ _ [6,65,192,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1518

theorem m2945_132 : Upper (D 10) (R 10) [18,192,72,288,132] 13 :=
  permutation_upper _ _ _ [6,72,192,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1676

theorem m2945_160 : Upper (D 10) (R 10) [18,192,72,288,160] 13 :=
  permutation_upper _ _ _ [6,96,192,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1789

theorem m2945_257 : Upper (D 10) (R 10) [18,192,72,288,257] 13 :=
  permutation_upper _ _ _ [6,65,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1531

theorem m2945_260 : Upper (D 10) (R 10) [18,192,72,288,260] 13 :=
  permutation_upper _ _ _ [6,72,384,144,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1715

theorem m2945_288 : Upper (D 10) (R 10) [18,192,72,288,288] 13 :=
  permutation_upper _ _ _ [6,96,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1818

theorem m2945_384 : Upper (D 10) (R 10) [18,192,72,288,384] 13 :=
  permutation_upper _ _ _ [6,192,320,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1841

def r2945 : Route 9 := (fun mask => (mask,id))

def c2945 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2945 : Upper (D 10) (R 10) [18,192,72,288] 13 := by
  apply FastRouting.sound _ _ [18,192,72,288] 13 (by decide) (choices 2) [5,33,36,129,132,160,257,260,288,384] r2945 c2945
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2945_5
  · exact m2945_33
  · exact m2945_36
  · exact m2945_129
  · exact m2945_132
  · exact m2945_160
  · exact m2945_257
  · exact m2945_260
  · exact m2945_288
  · exact m2945_384

theorem m2946_5 : Upper (D 10) (R 10) [18,192,72,384,5] 13 :=
  permutation_upper _ _ _ [6,9,80,192,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1131

theorem m2946_33 : Upper (D 10) (R 10) [18,192,72,384,33] 13 :=
  permutation_upper _ _ _ [6,33,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1268

theorem m2946_36 : Upper (D 10) (R 10) [18,192,72,384,36] 13 :=
  permutation_upper _ _ _ [6,40,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1408

theorem m2946_257 : Upper (D 10) (R 10) [18,192,72,384,257] 13 :=
  permutation_upper _ _ _ [6,65,384,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1535

theorem m2946_260 : Upper (D 10) (R 10) [18,192,72,384,260] 13 :=
  permutation_upper _ _ _ [6,72,384,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1718

theorem m2946_288 : Upper (D 10) (R 10) [18,192,72,384,288] 13 :=
  permutation_upper _ _ _ [6,96,384,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1825

def r2946 : Route 9 := (fun mask => (mask,id))

def c2946 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u2946 : Upper (D 10) (R 10) [18,192,72,384] 13 := by
  apply FastRouting.sound _ _ [18,192,72,384] 13 (by decide) (choices 2) [5,33,36,257,260,288] r2946 c2946
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2946_5
  · exact m2946_33
  · exact m2946_36
  · exact m2946_257
  · exact m2946_260
  · exact m2946_288

theorem m2947_5 : Upper (D 10) (R 10) [18,192,96,160,5] 13 :=
  permutation_upper _ _ _ [6,9,96,192,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1142

theorem m2947_9 : Upper (D 10) (R 10) [18,192,96,160,9] 13 :=
  permutation_upper _ _ _ [6,9,96,192,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1142

theorem m2947_12 : Upper (D 10) (R 10) [18,192,96,160,12] 13 :=
  permutation_upper _ _ _ [6,24,192,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1195

theorem m2947_33 : Upper (D 10) (R 10) [18,192,96,160,33] 13 :=
  permutation_upper _ _ _ [6,33,192,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1269

theorem m2947_36 : Upper (D 10) (R 10) [18,192,96,160,36] 13 :=
  permutation_upper _ _ _ [6,40,192,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1410

theorem m2947_40 : Upper (D 10) (R 10) [18,192,96,160,40] 13 :=
  permutation_upper _ _ _ [6,40,192,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1410

theorem m2947_257 : Upper (D 10) (R 10) [18,192,96,160,257] 13 :=
  permutation_upper _ _ _ [6,65,384,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1536

theorem m2947_260 : Upper (D 10) (R 10) [18,192,96,160,260] 13 :=
  permutation_upper _ _ _ [6,72,384,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1723

theorem m2947_264 : Upper (D 10) (R 10) [18,192,96,160,264] 13 :=
  permutation_upper _ _ _ [6,72,384,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1723

theorem m2947_288 : Upper (D 10) (R 10) [18,192,96,160,288] 13 :=
  permutation_upper _ _ _ [6,96,384,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1826

def r2947 : Route 9 := (fun mask => (mask,id))

def c2947 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u2947 : Upper (D 10) (R 10) [18,192,96,160] 13 := by
  apply FastRouting.sound _ _ [18,192,96,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r2947 c2947
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2947_5
  · exact m2947_9
  · exact m2947_12
  · exact m2947_33
  · exact m2947_36
  · exact m2947_40
  · exact m2947_257
  · exact m2947_260
  · exact m2947_264
  · exact m2947_288

theorem m2948_12 : Upper (D 10) (R 10) [18,192,96,257,12] 13 :=
  permutation_upper _ _ _ [6,24,192,96,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1196

theorem m2948_36 : Upper (D 10) (R 10) [18,192,96,257,36] 13 :=
  permutation_upper _ _ _ [6,40,192,96,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1411

theorem m2948_40 : Upper (D 10) (R 10) [18,192,96,257,40] 13 :=
  permutation_upper _ _ _ [6,40,192,257,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1417

theorem m2948_132 : Upper (D 10) (R 10) [18,192,96,257,132] 13 :=
  permutation_upper _ _ _ [6,72,192,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1678

theorem m2948_136 : Upper (D 10) (R 10) [18,192,96,257,136] 13 :=
  permutation_upper _ _ _ [6,72,192,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1680

theorem m2948_160 : Upper (D 10) (R 10) [18,192,96,257,160] 13 :=
  permutation_upper _ _ _ [6,96,192,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1790

theorem m2948_260 : Upper (D 10) (R 10) [18,192,96,257,260] 13 :=
  permutation_upper _ _ _ [6,72,384,160,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1720

theorem m2948_264 : Upper (D 10) (R 10) [18,192,96,257,264] 13 :=
  permutation_upper _ _ _ [6,72,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1705

theorem m2948_288 : Upper (D 10) (R 10) [18,192,96,257,288] 13 :=
  permutation_upper _ _ _ [6,96,384,65,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1813

theorem m2948_384 : Upper (D 10) (R 10) [18,192,96,257,384] 13 :=
  permutation_upper _ _ _ [6,192,320,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1840

def r2948 : Route 9 := (fun mask => (mask,id))

def c2948 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2948 : Upper (D 10) (R 10) [18,192,96,257] 13 := by
  apply FastRouting.sound _ _ [18,192,96,257] 13 (by decide) (choices 2) [12,36,40,132,136,160,260,264,288,384] r2948 c2948
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2948_12
  · exact m2948_36
  · exact m2948_40
  · exact m2948_132
  · exact m2948_136
  · exact m2948_160
  · exact m2948_260
  · exact m2948_264
  · exact m2948_288
  · exact m2948_384

theorem m2949_9 : Upper (D 10) (R 10) [18,192,96,260,9] 13 :=
  permutation_upper _ _ _ [6,9,80,384,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1133

theorem m2949_33 : Upper (D 10) (R 10) [18,192,96,260,33] 13 :=
  permutation_upper _ _ _ [6,33,192,96,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1270

theorem m2949_40 : Upper (D 10) (R 10) [18,192,96,260,40] 13 :=
  permutation_upper _ _ _ [6,40,192,272,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1423

theorem m2949_129 : Upper (D 10) (R 10) [18,192,96,260,129] 13 :=
  permutation_upper _ _ _ [6,65,192,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1519

theorem m2949_136 : Upper (D 10) (R 10) [18,192,96,260,136] 13 :=
  permutation_upper _ _ _ [6,72,192,272,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1685

theorem m2949_160 : Upper (D 10) (R 10) [18,192,96,260,160] 13 :=
  permutation_upper _ _ _ [6,96,192,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1791

theorem m2949_257 : Upper (D 10) (R 10) [18,192,96,260,257] 13 :=
  permutation_upper _ _ _ [6,65,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1530

theorem m2949_264 : Upper (D 10) (R 10) [18,192,96,260,264] 13 :=
  permutation_upper _ _ _ [6,72,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1707

theorem m2949_288 : Upper (D 10) (R 10) [18,192,96,260,288] 13 :=
  permutation_upper _ _ _ [6,96,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1816

theorem m2949_384 : Upper (D 10) (R 10) [18,192,96,260,384] 13 :=
  permutation_upper _ _ _ [6,192,320,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1841

def r2949 : Route 9 := (fun mask => (mask,id))

def c2949 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2949 : Upper (D 10) (R 10) [18,192,96,260] 13 := by
  apply FastRouting.sound _ _ [18,192,96,260] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r2949 c2949
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2949_9
  · exact m2949_33
  · exact m2949_40
  · exact m2949_129
  · exact m2949_136
  · exact m2949_160
  · exact m2949_257
  · exact m2949_264
  · exact m2949_288
  · exact m2949_384

theorem m2950_5 : Upper (D 10) (R 10) [18,192,96,288,5] 13 :=
  permutation_upper _ _ _ [6,9,96,192,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1143

theorem m2950_9 : Upper (D 10) (R 10) [18,192,96,288,9] 13 :=
  permutation_upper _ _ _ [6,9,96,384,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1146

theorem m2950_12 : Upper (D 10) (R 10) [18,192,96,288,12] 13 :=
  permutation_upper _ _ _ [6,24,192,96,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1197

theorem m2950_33 : Upper (D 10) (R 10) [18,192,96,288,33] 13 :=
  permutation_upper _ _ _ [6,33,192,96,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1271

theorem m2950_36 : Upper (D 10) (R 10) [18,192,96,288,36] 13 :=
  permutation_upper _ _ _ [6,40,192,96,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1412

theorem m2950_40 : Upper (D 10) (R 10) [18,192,96,288,40] 13 :=
  permutation_upper _ _ _ [6,40,192,288,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1429

theorem m2950_129 : Upper (D 10) (R 10) [18,192,96,288,129] 13 :=
  permutation_upper _ _ _ [6,65,192,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1520

theorem m2950_132 : Upper (D 10) (R 10) [18,192,96,288,132] 13 :=
  permutation_upper _ _ _ [6,72,192,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1679

theorem m2950_136 : Upper (D 10) (R 10) [18,192,96,288,136] 13 :=
  permutation_upper _ _ _ [6,72,192,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1688

theorem m2950_160 : Upper (D 10) (R 10) [18,192,96,288,160] 13 :=
  permutation_upper _ _ _ [6,96,192,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1792

theorem m2950_257 : Upper (D 10) (R 10) [18,192,96,288,257] 13 :=
  permutation_upper _ _ _ [6,65,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1532

theorem m2950_260 : Upper (D 10) (R 10) [18,192,96,288,260] 13 :=
  permutation_upper _ _ _ [6,72,384,160,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1721

theorem m2950_264 : Upper (D 10) (R 10) [18,192,96,288,264] 13 :=
  permutation_upper _ _ _ [6,72,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1709

theorem m2950_288 : Upper (D 10) (R 10) [18,192,96,288,288] 13 :=
  permutation_upper _ _ _ [6,96,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1819

theorem m2950_384 : Upper (D 10) (R 10) [18,192,96,288,384] 13 :=
  permutation_upper _ _ _ [6,192,320,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1842

def r2950 : Route 9 := (fun mask => (mask,id))

def c2950 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2950 : Upper (D 10) (R 10) [18,192,96,288] 13 := by
  apply FastRouting.sound _ _ [18,192,96,288] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160,257,260,264,288,384] r2950 c2950
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2950_5
  · exact m2950_9
  · exact m2950_12
  · exact m2950_33
  · exact m2950_36
  · exact m2950_40
  · exact m2950_129
  · exact m2950_132
  · exact m2950_136
  · exact m2950_160
  · exact m2950_257
  · exact m2950_260
  · exact m2950_264
  · exact m2950_288
  · exact m2950_384

theorem m2951_5 : Upper (D 10) (R 10) [18,192,96,384,5] 13 :=
  permutation_upper _ _ _ [6,9,96,192,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1144

theorem m2951_9 : Upper (D 10) (R 10) [18,192,96,384,9] 13 :=
  permutation_upper _ _ _ [6,9,192,320,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1150

theorem m2951_12 : Upper (D 10) (R 10) [18,192,96,384,12] 13 :=
  permutation_upper _ _ _ [6,24,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1198

theorem m2951_33 : Upper (D 10) (R 10) [18,192,96,384,33] 13 :=
  permutation_upper _ _ _ [6,33,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1272

theorem m2951_36 : Upper (D 10) (R 10) [18,192,96,384,36] 13 :=
  permutation_upper _ _ _ [6,40,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1413

theorem m2951_40 : Upper (D 10) (R 10) [18,192,96,384,40] 13 :=
  permutation_upper _ _ _ [6,40,192,320,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1435

theorem m2951_257 : Upper (D 10) (R 10) [18,192,96,384,257] 13 :=
  permutation_upper _ _ _ [6,65,384,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1537

theorem m2951_260 : Upper (D 10) (R 10) [18,192,96,384,260] 13 :=
  permutation_upper _ _ _ [6,72,384,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1724

theorem m2951_264 : Upper (D 10) (R 10) [18,192,96,384,264] 13 :=
  permutation_upper _ _ _ [6,72,384,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1726

theorem m2951_288 : Upper (D 10) (R 10) [18,192,96,384,288] 13 :=
  permutation_upper _ _ _ [6,96,384,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1827

def r2951 : Route 9 := (fun mask => (mask,id))

def c2951 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u2951 : Upper (D 10) (R 10) [18,192,96,384] 13 := by
  apply FastRouting.sound _ _ [18,192,96,384] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r2951 c2951
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2951_5
  · exact m2951_9
  · exact m2951_12
  · exact m2951_33
  · exact m2951_36
  · exact m2951_40
  · exact m2951_257
  · exact m2951_260
  · exact m2951_264
  · exact m2951_288

def b2952 : PairBound 9 := { available := 300, camps := [{ cop := 1, region := 4, targets := 288 }], pairs := [(2,5),(2,8)], upper := (rows 19 194 196 265 316 300 364 428 300), lower := (rows 19 194 196 265 16 32 64 128 256), losses := [] }

theorem u2952 : Upper (D 10) (R 10) [18,192,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2952 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2953 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 4, targets := 288 }], pairs := [(2,5),(2,8)], upper := (rows 19 194 196 268 313 297 361 425 297), lower := (rows 19 194 196 268 16 32 64 128 256), losses := [] }

theorem u2953 : Upper (D 10) (R 10) [18,192,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2953 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2954 : PairBound 9 := { available := 301, camps := [{ cop := 1, region := 4, targets := 288 }], pairs := [(2,5),(2,8)], upper := (rows 19 194 196 296 317 301 365 429 301), lower := (rows 19 194 196 296 16 32 64 128 256), losses := [] }

theorem u2954 : Upper (D 10) (R 10) [18,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2954 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2955_12 : Upper (D 10) (R 10) [18,192,257,288,12] 13 :=
  permutation_upper _ _ _ [6,24,192,257,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1201

theorem m2955_36 : Upper (D 10) (R 10) [18,192,257,288,36] 13 :=
  permutation_upper _ _ _ [6,40,192,257,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1419

theorem m2955_40 : Upper (D 10) (R 10) [18,192,257,288,40] 13 :=
  permutation_upper _ _ _ [6,40,192,288,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1430

theorem m2955_68 : Upper (D 10) (R 10) [18,192,257,288,68] 13 :=
  permutation_upper _ _ _ [6,72,192,257,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1681

theorem m2955_72 : Upper (D 10) (R 10) [18,192,257,288,72] 13 :=
  permutation_upper _ _ _ [6,72,192,288,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1689

theorem m2955_96 : Upper (D 10) (R 10) [18,192,257,288,96] 13 :=
  permutation_upper _ _ _ [6,96,192,257,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1793

theorem m2955_192 : Upper (D 10) (R 10) [18,192,257,288,192] 13 :=
  permutation_upper _ _ _ [6,192,192,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1832

def r2955 : Route 9 := (fun mask => match mask with | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2955 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u2955 : Upper (D 10) (R 10) [18,192,257,288] 13 := by
  apply FastRouting.sound _ _ [18,192,257,288] 13 (by decide) (choices 2) [12,36,40,68,72,96,192] r2955 c2955
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2955_12
  · exact m2955_36
  · exact m2955_40
  · exact m2955_68
  · exact m2955_72
  · exact m2955_96
  · exact m2955_192

theorem m2956_12 : Upper (D 10) (R 10) [18,192,257,320,12] 13 :=
  permutation_upper _ _ _ [6,24,192,257,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1202

theorem m2956_36 : Upper (D 10) (R 10) [18,192,257,320,36] 13 :=
  permutation_upper _ _ _ [6,40,192,257,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1420

theorem m2956_40 : Upper (D 10) (R 10) [18,192,257,320,40] 13 :=
  permutation_upper _ _ _ [6,40,192,320,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1436

theorem m2956_132 : Upper (D 10) (R 10) [18,192,257,320,132] 13 :=
  permutation_upper _ _ _ [6,72,192,257,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1682

theorem m2956_136 : Upper (D 10) (R 10) [18,192,257,320,136] 13 :=
  permutation_upper _ _ _ [6,72,192,384,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1692

theorem m2956_160 : Upper (D 10) (R 10) [18,192,257,320,160] 13 :=
  permutation_upper _ _ _ [6,96,192,257,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1794

def r2956 : Route 9 := (fun mask => (mask,id))

def c2956 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u2956 : Upper (D 10) (R 10) [18,192,257,320] 13 := by
  apply FastRouting.sound _ _ [18,192,257,320] 13 (by decide) (choices 2) [12,36,40,132,136,160] r2956 c2956
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2956_12
  · exact m2956_36
  · exact m2956_40
  · exact m2956_132
  · exact m2956_136
  · exact m2956_160

theorem m2957_5 : Upper (D 10) (R 10) [18,192,288,320,5] 13 :=
  permutation_upper _ _ _ [6,9,96,384,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1147

theorem m2957_9 : Upper (D 10) (R 10) [18,192,288,320,9] 13 :=
  permutation_upper _ _ _ [6,9,192,320,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1150

theorem m2957_12 : Upper (D 10) (R 10) [18,192,288,320,12] 13 :=
  permutation_upper _ _ _ [6,24,192,288,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1204

theorem m2957_33 : Upper (D 10) (R 10) [18,192,288,320,33] 13 :=
  permutation_upper _ _ _ [6,33,192,288,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1279

theorem m2957_36 : Upper (D 10) (R 10) [18,192,288,320,36] 13 :=
  permutation_upper _ _ _ [6,40,192,288,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1432

theorem m2957_40 : Upper (D 10) (R 10) [18,192,288,320,40] 13 :=
  permutation_upper _ _ _ [6,40,192,320,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1437

theorem m2957_129 : Upper (D 10) (R 10) [18,192,288,320,129] 13 :=
  permutation_upper _ _ _ [6,65,192,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1521

theorem m2957_132 : Upper (D 10) (R 10) [18,192,288,320,132] 13 :=
  permutation_upper _ _ _ [6,72,192,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1690

theorem m2957_136 : Upper (D 10) (R 10) [18,192,288,320,136] 13 :=
  permutation_upper _ _ _ [6,72,192,384,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1693

theorem m2957_160 : Upper (D 10) (R 10) [18,192,288,320,160] 13 :=
  permutation_upper _ _ _ [6,96,192,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1795

def r2957 : Route 9 := (fun mask => (mask,id))

def c2957 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u2957 : Upper (D 10) (R 10) [18,192,288,320] 13 := by
  apply FastRouting.sound _ _ [18,192,288,320] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r2957 c2957
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2957_5
  · exact m2957_9
  · exact m2957_12
  · exact m2957_33
  · exact m2957_36
  · exact m2957_40
  · exact m2957_129
  · exact m2957_132
  · exact m2957_136
  · exact m2957_160

theorem m2958_5 : Upper (D 10) (R 10) [18,192,320,384,5] 13 :=
  permutation_upper _ _ _ [6,9,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1151

theorem m2958_9 : Upper (D 10) (R 10) [18,192,320,384,9] 13 :=
  permutation_upper _ _ _ [6,9,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1151

theorem m2958_12 : Upper (D 10) (R 10) [18,192,320,384,12] 13 :=
  permutation_upper _ _ _ [6,24,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1205

theorem m2958_33 : Upper (D 10) (R 10) [18,192,320,384,33] 13 :=
  permutation_upper _ _ _ [6,33,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1280

theorem m2958_36 : Upper (D 10) (R 10) [18,192,320,384,36] 13 :=
  permutation_upper _ _ _ [6,40,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1438

theorem m2958_40 : Upper (D 10) (R 10) [18,192,320,384,40] 13 :=
  permutation_upper _ _ _ [6,40,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1438

def r2958 : Route 9 := (fun mask => (mask,id))

def c2958 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u2958 : Upper (D 10) (R 10) [18,192,320,384] 13 := by
  apply FastRouting.sound _ _ [18,192,320,384] 13 (by decide) (choices 2) [5,9,12,33,36,40] r2958 c2958
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2958_5
  · exact m2958_9
  · exact m2958_12
  · exact m2958_33
  · exact m2958_36
  · exact m2958_40

def b2959 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 44 76 464 496 464 464 464), lower := (rows 35 35 44 76 16 32 64 128 256), losses := [] }

theorem u2959 : Upper (D 10) (R 10) [34,33,40,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2959 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2960 : PairBound 9 := { available := 468, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 44 200 468 500 468 468 468), lower := (rows 35 35 44 200 16 32 64 128 256), losses := [] }

theorem u2960 : Upper (D 10) (R 10) [34,33,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2960 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2961 : PairBound 9 := { available := 496, camps := [{ cop := 5, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 76 140 496 496 496 496 496), lower := (rows 35 35 76 140 16 32 64 128 256), losses := [] }

theorem u2961 : Upper (D 10) (R 10) [34,33,72,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2961 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2962 : PairBound 9 := { available := 468, camps := [{ cop := 3, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 76 168 468 500 468 468 468), lower := (rows 35 35 76 168 16 32 64 128 256), losses := [] }

theorem u2962 : Upper (D 10) (R 10) [34,33,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2962 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2963 : PairBound 9 := { available := 500, camps := [{ cop := 5, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 76 392 500 500 500 500 500), lower := (rows 35 35 76 392 16 32 64 128 256), losses := [] }

theorem u2963 : Upper (D 10) (R 10) [34,33,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2963 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2964 : PairBound 9 := { available := 412, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 100 200 412 444 476 412 412), lower := (rows 35 35 100 200 16 32 64 128 256), losses := [] }

theorem u2964 : Upper (D 10) (R 10) [34,33,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2964 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2965 : PairBound 9 := { available := 476, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 100 392 476 508 476 476 476), lower := (rows 35 35 100 392 16 32 64 128 256), losses := [] }

theorem u2965 : Upper (D 10) (R 10) [34,33,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2965 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2966 : PairBound 9 := { available := 444, camps := [{ cop := 5, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 196 328 444 444 508 444 444), lower := (rows 35 35 196 328 16 32 64 128 256), losses := [] }

theorem u2966 : Upper (D 10) (R 10) [34,33,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2966 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2967 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 44 73 464 496 464 464 464), lower := (rows 35 38 44 73 16 32 64 128 256), losses := [] }

theorem u2967 : Upper (D 10) (R 10) [34,36,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2967 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2968 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 44 200 465 497 465 465 465), lower := (rows 35 38 44 200 16 32 64 128 256), losses := [] }

theorem u2968 : Upper (D 10) (R 10) [34,36,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2968 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2969 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 38 69 104 408 440 472 408 408), lower := (rows 35 38 69 104 16 32 64 128 256), losses := [] }

theorem u2969 : Upper (D 10) (R 10) [34,36,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2969 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2970 : PairBound 9 := { available := 472, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 168 472 504 472 472 472), lower := (rows 35 38 69 168 16 32 64 128 256), losses := [] }

theorem u2970 : Upper (D 10) (R 10) [34,36,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2970 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2971 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 200 440 440 504 440 440), lower := (rows 35 38 69 200 16 32 64 128 256), losses := [] }

theorem u2971 : Upper (D 10) (R 10) [34,36,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2971 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2972 : PairBound 9 := { available := 504, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 392 504 504 504 504 504), lower := (rows 35 38 69 392 16 32 64 128 256), losses := [] }

theorem u2972 : Upper (D 10) (R 10) [34,36,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2972 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2973 : PairBound 9 := { available := 496, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 137 496 496 496 496 496), lower := (rows 35 38 76 137 16 32 64 128 256), losses := [] }

theorem u2973 : Upper (D 10) (R 10) [34,36,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2973 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2974 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 168 465 497 465 465 465), lower := (rows 35 38 76 168 16 32 64 128 256), losses := [] }

theorem u2974 : Upper (D 10) (R 10) [34,36,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2974 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2975 : PairBound 9 := { available := 497, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 392 497 497 497 497 497), lower := (rows 35 38 76 392 16 32 64 128 256), losses := [] }

theorem u2975 : Upper (D 10) (R 10) [34,36,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2975 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2976 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 38 100 73 408 440 472 408 408), lower := (rows 35 38 100 73 16 32 64 128 256), losses := [] }

theorem u2976 : Upper (D 10) (R 10) [34,36,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2976 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2977 : PairBound 9 := { available := 472, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 100 137 472 504 472 472 472), lower := (rows 35 38 100 137 16 32 64 128 256), losses := [] }

theorem u2977 : Upper (D 10) (R 10) [34,36,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2977 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2978 : PairBound 9 := { available := 409, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 100 200 409 441 473 409 409), lower := (rows 35 38 100 200 16 32 64 128 256), losses := [] }

theorem u2978 : Upper (D 10) (R 10) [34,36,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2978 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2979 : PairBound 9 := { available := 473, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 100 392 473 505 473 473 473), lower := (rows 35 38 100 392 16 32 64 128 256), losses := [] }

theorem u2979 : Upper (D 10) (R 10) [34,36,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2979 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2980 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 73 440 440 504 440 440), lower := (rows 35 38 196 73 16 32 64 128 256), losses := [] }

theorem u2980 : Upper (D 10) (R 10) [34,36,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2980 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2981 : PairBound 9 := { available := 409, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 104 409 441 473 409 409), lower := (rows 35 38 196 104 16 32 64 128 256), losses := [] }

theorem u2981 : Upper (D 10) (R 10) [34,36,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2981 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2982 : PairBound 9 := { available := 504, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 265 504 504 504 504 504), lower := (rows 35 38 196 265 16 32 64 128 256), losses := [] }

theorem u2982 : Upper (D 10) (R 10) [34,36,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2982 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2983 : PairBound 9 := { available := 473, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 296 473 505 473 473 473), lower := (rows 35 38 196 296 16 32 64 128 256), losses := [] }

theorem u2983 : Upper (D 10) (R 10) [34,36,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2983 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2984 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 328 441 441 505 441 441), lower := (rows 35 38 196 328 16 32 64 128 256), losses := [] }

theorem u2984 : Upper (D 10) (R 10) [34,36,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2984 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2985 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 44 73 468 484 452 452 452), lower := (rows 35 50 44 73 16 32 64 128 256), losses := [] }

theorem u2985 : Upper (D 10) (R 10) [34,48,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2985 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2986 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 44 76 465 481 449 449 449), lower := (rows 35 50 44 76 16 32 64 128 256), losses := [] }

theorem u2986 : Upper (D 10) (R 10) [34,48,40,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2986 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2987 : PairBound 9 := { available := 453, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 44 200 469 485 453 453 453), lower := (rows 35 50 44 200 16 32 64 128 256), losses := [] }

theorem u2987 : Upper (D 10) (R 10) [34,48,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2987 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2988 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 69 104 412 428 460 396 396), lower := (rows 35 50 69 104 16 32 64 128 256), losses := [] }

theorem u2988 : Upper (D 10) (R 10) [34,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2988 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2989 : PairBound 9 := { available := 488, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 69 140 504 488 488 488 488), lower := (rows 35 50 69 140 16 32 64 128 256), losses := [] }

theorem u2989 : Upper (D 10) (R 10) [34,48,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2989 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2990 : PairBound 9 := { available := 460, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 69 168 476 492 460 460 460), lower := (rows 35 50 69 168 16 32 64 128 256), losses := [] }

theorem u2990 : Upper (D 10) (R 10) [34,48,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2990 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2991 : PairBound 9 := { available := 428, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 69 200 444 428 492 428 428), lower := (rows 35 50 69 200 16 32 64 128 256), losses := [] }

theorem u2991 : Upper (D 10) (R 10) [34,48,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2991 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2992 : PairBound 9 := { available := 492, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 69 392 508 492 492 492 492), lower := (rows 35 50 69 392 16 32 64 128 256), losses := [] }

theorem u2992 : Upper (D 10) (R 10) [34,48,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2992 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2993 : PairBound 9 := { available := 481, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 76 140 497 481 481 481 481), lower := (rows 35 50 76 140 16 32 64 128 256), losses := [] }

theorem u2993 : Upper (D 10) (R 10) [34,48,72,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2993 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2994 : PairBound 9 := { available := 453, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 76 168 469 485 453 453 453), lower := (rows 35 50 76 168 16 32 64 128 256), losses := [] }

theorem u2994 : Upper (D 10) (R 10) [34,48,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2994 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2995 : PairBound 9 := { available := 485, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 76 392 501 485 485 485 485), lower := (rows 35 50 76 392 16 32 64 128 256), losses := [] }

theorem u2995 : Upper (D 10) (R 10) [34,48,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2995 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2996 : PairBound 9 := { available := 397, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 100 200 413 429 461 397 397), lower := (rows 35 50 100 200 16 32 64 128 256), losses := [] }

theorem u2996 : Upper (D 10) (R 10) [34,48,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2996 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2997 : PairBound 9 := { available := 461, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 100 392 477 493 461 461 461), lower := (rows 35 50 100 392 16 32 64 128 256), losses := [] }

theorem u2997 : Upper (D 10) (R 10) [34,48,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2997 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2998 : PairBound 9 := { available := 429, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 50 196 328 445 429 493 429 429), lower := (rows 35 50 196 328 16 32 64 128 256), losses := [] }

theorem u2998 : Upper (D 10) (R 10) [34,48,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2998 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2999 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 67 44 76 432 432 496 432 432), lower := (rows 35 67 44 76 16 32 64 128 256), losses := [] }

theorem u2999 : Upper (D 10) (R 10) [34,65,40,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2999 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2999
end Delivery.IrregularNine14.P10
