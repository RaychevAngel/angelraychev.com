import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0287
import IrregularNine14P08C0288
import IrregularNine14P08C0289
import IrregularNine14P08C0290
import IrregularNine14P08C0292
import IrregularNine14P08C0293
import IrregularNine14P08C0294
import IrregularNine14P08C0295
import IrregularNine14P08C0296
import IrregularNine14P08C0297
import IrregularNine14P08C0298

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m23280_3 : Upper (D 8) (R 8) [288,68,160,144,3] 13 :=
  permutation_upper _ _ _ [288,5,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17317

theorem m23280_9 : Upper (D 8) (R 8) [288,68,160,144,9] 13 :=
  permutation_upper _ _ _ [288,5,66,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17237

theorem m23280_10 : Upper (D 8) (R 8) [288,68,160,144,10] 13 :=
  permutation_upper _ _ _ [288,12,66,144,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17539

theorem m23280_33 : Upper (D 8) (R 8) [288,68,160,144,33] 13 :=
  permutation_upper _ _ _ [288,33,66,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17616

theorem m23280_34 : Upper (D 8) (R 8) [288,68,160,144,34] 13 :=
  permutation_upper _ _ _ [288,36,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17721

theorem m23280_40 : Upper (D 8) (R 8) [288,68,160,144,40] 13 :=
  permutation_upper _ _ _ [288,36,66,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17677

theorem m23280_65 : Upper (D 8) (R 8) [288,68,160,144,65] 13 :=
  permutation_upper _ _ _ [288,65,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17763

theorem m23280_66 : Upper (D 8) (R 8) [288,68,160,144,66] 13 :=
  permutation_upper _ _ _ [288,68,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17775

theorem m23280_72 : Upper (D 8) (R 8) [288,68,160,144,72] 13 :=
  permutation_upper _ _ _ [288,68,130,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17777

theorem m23280_96 : Upper (D 8) (R 8) [288,68,160,144,96] 13 :=
  permutation_upper _ _ _ [288,68,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17782

def r23280 : Route 9 := (fun mask => (mask,id))

def c23280 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u23280 : Upper (D 8) (R 8) [288,68,160,144] 13 := by
  apply FastRouting.sound _ _ [288,68,160,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r23280 c23280
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23280_3
  · exact m23280_9
  · exact m23280_10
  · exact m23280_33
  · exact m23280_34
  · exact m23280_40
  · exact m23280_65
  · exact m23280_66
  · exact m23280_72
  · exact m23280_96

def b23281 : PairBound 9 := { available := 91, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 289 70 164 168 91 123 91 219 347), lower := (rows 289 70 164 168 16 32 64 128 256), losses := [] }

theorem u23281 : Upper (D 8) (R 8) [288,68,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23282_3 : Upper (D 8) (R 8) [288,68,160,192,3] 13 :=
  permutation_upper _ _ _ [288,5,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17319

theorem m23282_9 : Upper (D 8) (R 8) [288,68,160,192,9] 13 :=
  permutation_upper _ _ _ [288,5,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17404

theorem m23282_10 : Upper (D 8) (R 8) [288,68,160,192,10] 13 :=
  permutation_upper _ _ _ [288,12,80,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17567

theorem m23282_33 : Upper (D 8) (R 8) [288,68,160,192,33] 13 :=
  permutation_upper _ _ _ [288,33,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17620

theorem m23282_34 : Upper (D 8) (R 8) [288,68,160,192,34] 13 :=
  permutation_upper _ _ _ [288,36,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17722

theorem m23282_40 : Upper (D 8) (R 8) [288,68,160,192,40] 13 :=
  permutation_upper _ _ _ [288,36,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17745

def r23282 : Route 9 := (fun mask => (mask,id))

def c23282 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23282 : Upper (D 8) (R 8) [288,68,160,192] 13 := by
  apply FastRouting.sound _ _ [288,68,160,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23282 c23282
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23282_3
  · exact m23282_9
  · exact m23282_10
  · exact m23282_33
  · exact m23282_34
  · exact m23282_40

def b23283 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 196 168 59 59 123 187 315), lower := (rows 289 70 196 168 16 32 64 128 256), losses := [] }

theorem u23283 : Upper (D 8) (R 8) [288,68,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23284_3 : Upper (D 8) (R 8) [288,80,96,160,3] 13 :=
  permutation_upper _ _ _ [288,5,66,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17238

theorem m23284_5 : Upper (D 8) (R 8) [288,80,96,160,5] 13 :=
  permutation_upper _ _ _ [288,5,96,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17357

theorem m23284_6 : Upper (D 8) (R 8) [288,80,96,160,6] 13 :=
  permutation_upper _ _ _ [288,12,66,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17536

theorem m23284_9 : Upper (D 8) (R 8) [288,80,96,160,9] 13 :=
  permutation_upper _ _ _ [288,5,96,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17370

theorem m23284_10 : Upper (D 8) (R 8) [288,80,96,160,10] 13 :=
  permutation_upper _ _ _ [288,12,66,160,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17545

theorem m23284_12 : Upper (D 8) (R 8) [288,80,96,160,12] 13 :=
  permutation_upper _ _ _ [288,12,96,160,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17571

theorem m23284_129 : Upper (D 8) (R 8) [288,80,96,160,129] 13 :=
  permutation_upper _ _ _ [288,65,96,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17769

theorem m23284_130 : Upper (D 8) (R 8) [288,80,96,160,130] 13 :=
  permutation_upper _ _ _ [288,68,130,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17778

theorem m23284_132 : Upper (D 8) (R 8) [288,80,96,160,132] 13 :=
  permutation_upper _ _ _ [288,68,136,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17780

theorem m23284_136 : Upper (D 8) (R 8) [288,80,96,160,136] 13 :=
  permutation_upper _ _ _ [288,68,96,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17776

def r23284 : Route 9 := (fun mask => (mask,id))

def c23284 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23284 : Upper (D 8) (R 8) [288,80,96,160] 13 := by
  apply FastRouting.sound _ _ [288,80,96,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136] r23284 c23284
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23284_3
  · exact m23284_5
  · exact m23284_6
  · exact m23284_9
  · exact m23284_10
  · exact m23284_12
  · exact m23284_129
  · exact m23284_130
  · exact m23284_132
  · exact m23284_136

theorem m23285_3 : Upper (D 8) (R 8) [288,80,160,192,3] 13 :=
  permutation_upper _ _ _ [288,5,66,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17246

theorem m23285_5 : Upper (D 8) (R 8) [288,80,160,192,5] 13 :=
  permutation_upper _ _ _ [288,5,96,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17371

theorem m23285_6 : Upper (D 8) (R 8) [288,80,160,192,6] 13 :=
  permutation_upper _ _ _ [288,12,66,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17548

theorem m23285_9 : Upper (D 8) (R 8) [288,80,160,192,9] 13 :=
  permutation_upper _ _ _ [288,5,192,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17402

theorem m23285_10 : Upper (D 8) (R 8) [288,80,160,192,10] 13 :=
  permutation_upper _ _ _ [288,12,66,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17550

theorem m23285_12 : Upper (D 8) (R 8) [288,80,160,192,12] 13 :=
  permutation_upper _ _ _ [288,12,96,192,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17575

theorem m23285_33 : Upper (D 8) (R 8) [288,80,160,192,33] 13 :=
  permutation_upper _ _ _ [288,33,66,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17619

theorem m23285_34 : Upper (D 8) (R 8) [288,80,160,192,34] 13 :=
  permutation_upper _ _ _ [288,36,66,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17685

theorem m23285_36 : Upper (D 8) (R 8) [288,80,160,192,36] 13 :=
  permutation_upper _ _ _ [288,36,96,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17736

theorem m23285_40 : Upper (D 8) (R 8) [288,80,160,192,40] 13 :=
  permutation_upper _ _ _ [288,36,192,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17743

def r23285 : Route 9 := (fun mask => (mask,id))

def c23285 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23285 : Upper (D 8) (R 8) [288,80,160,192] 13 := by
  apply FastRouting.sound _ _ [288,80,160,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r23285 c23285
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23285_3
  · exact m23285_5
  · exact m23285_6
  · exact m23285_9
  · exact m23285_10
  · exact m23285_12
  · exact m23285_33
  · exact m23285_34
  · exact m23285_36
  · exact m23285_40

theorem m23286_3 : Upper (D 8) (R 8) [288,96,160,192,3] 13 :=
  permutation_upper _ _ _ [288,5,96,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17375

theorem m23286_5 : Upper (D 8) (R 8) [288,96,160,192,5] 13 :=
  permutation_upper _ _ _ [288,5,96,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17375

theorem m23286_6 : Upper (D 8) (R 8) [288,96,160,192,6] 13 :=
  permutation_upper _ _ _ [288,12,96,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17572

theorem m23286_9 : Upper (D 8) (R 8) [288,96,160,192,9] 13 :=
  permutation_upper _ _ _ [288,5,192,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17405

theorem m23286_10 : Upper (D 8) (R 8) [288,96,160,192,10] 13 :=
  permutation_upper _ _ _ [288,12,96,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17576

theorem m23286_12 : Upper (D 8) (R 8) [288,96,160,192,12] 13 :=
  permutation_upper _ _ _ [288,12,96,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17576

def r23286 : Route 9 := (fun mask => (mask,id))

def c23286 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23286 : Upper (D 8) (R 8) [288,96,160,192] 13 := by
  apply FastRouting.sound _ _ [288,96,160,192] 13 (by decide) (choices 2) [3,5,6,9,10,12] r23286 c23286
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23286_3
  · exact m23286_5
  · exact m23286_6
  · exact m23286_9
  · exact m23286_10
  · exact m23286_12

def b23287 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 7 104 184 184 248 184 440), lower := (rows 321 7 7 104 16 32 64 128 256), losses := [] }

theorem u23287 : Upper (D 8) (R 8) [320,5,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23288 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 7 168 248 248 248 248 504), lower := (rows 321 7 7 168 16 32 64 128 256), losses := [] }

theorem u23288 : Upper (D 8) (R 8) [320,5,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23289 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 7 200 184 184 248 184 440), lower := (rows 321 7 7 200 16 32 64 128 256), losses := [] }

theorem u23289 : Upper (D 8) (R 8) [320,5,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23290 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 26 240 224 224 224 480), lower := (rows 321 7 13 26 16 32 64 128 256), losses := [] }

theorem u23290 : Upper (D 8) (R 8) [320,5,9,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23290 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23291 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 42 240 240 240 240 496), lower := (rows 321 7 13 42 16 32 64 128 256), losses := [] }

theorem u23291 : Upper (D 8) (R 8) [320,5,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23292 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 74 176 176 240 176 432), lower := (rows 321 7 13 74 16 32 64 128 256), losses := [] }

theorem u23292 : Upper (D 8) (R 8) [320,5,9,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23293 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 104 178 178 242 178 434), lower := (rows 321 7 13 104 16 32 64 128 256), losses := [] }

theorem u23293 : Upper (D 8) (R 8) [320,5,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23294 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 138 240 240 240 240 496), lower := (rows 321 7 13 138 16 32 64 128 256), losses := [] }

theorem u23294 : Upper (D 8) (R 8) [320,5,9,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23295 : PairBound 9 := { available := 242, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 13 168 242 242 242 242 498), lower := (rows 321 7 13 168 16 32 64 128 256), losses := [] }

theorem u23295 : Upper (D 8) (R 8) [320,5,9,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23296 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 13 200 178 178 242 178 434), lower := (rows 321 7 13 200 16 32 64 128 256), losses := [] }

theorem u23296 : Upper (D 8) (R 8) [320,5,9,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23297 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 25 240 224 224 224 480), lower := (rows 321 7 14 25 16 32 64 128 256), losses := [] }

theorem u23297 : Upper (D 8) (R 8) [320,5,10,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23298 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 41 240 240 240 240 496), lower := (rows 321 7 14 41 16 32 64 128 256), losses := [] }

theorem u23298 : Upper (D 8) (R 8) [320,5,10,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23299 : Route 9 := (fun mask => (mask,id))

def c23299 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23299 : Upper (D 8) (R 8) [320,5,10,48] 13 := by
  apply FastRouting.sound _ _ [320,5,10,48] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23299 c23299
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u17825
  · exact u17826
  · exact u17827
  · exact u17828
  · exact u17829
  · exact u17830

def b23300 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 73 176 176 240 176 432), lower := (rows 321 7 14 73 16 32 64 128 256), losses := [] }

theorem u23300 : Upper (D 8) (R 8) [320,5,10,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23300 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23301 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 14 88 177 161 225 161 417), lower := (rows 321 7 14 88 16 32 64 128 256), losses := [] }

theorem u23301 : Upper (D 8) (R 8) [320,5,10,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23302 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 14 104 177 177 241 177 433), lower := (rows 321 7 14 104 16 32 64 128 256), losses := [] }

theorem u23302 : Upper (D 8) (R 8) [320,5,10,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23303 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 14 137 240 240 240 240 496), lower := (rows 321 7 14 137 16 32 64 128 256), losses := [] }

theorem u23303 : Upper (D 8) (R 8) [320,5,10,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r23304 : Route 9 := (fun mask => (mask,id))

def c23304 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23304 : Upper (D 8) (R 8) [320,5,10,144] 13 := by
  apply FastRouting.sound _ _ [320,5,10,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23304 c23304
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u17841
  · exact u17842
  · exact u17843
  · exact u17844
  · exact u17845
  · exact u17846

def r23305 : Route 9 := (fun mask => (mask,id))

def c23305 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23305 : Upper (D 8) (R 8) [320,5,10,160] 13 := by
  apply FastRouting.sound _ _ [320,5,10,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23305 c23305
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u17847
  · exact u17848
  · exact u17849
  · exact u17850
  · exact u17851
  · exact u17852

def b23306 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 14 200 177 177 241 177 433), lower := (rows 321 7 14 200 16 32 64 128 256), losses := [] }

theorem u23306 : Upper (D 8) (R 8) [320,5,10,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23307 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 21 42 248 232 232 232 488), lower := (rows 321 7 21 42 16 32 64 128 256), losses := [] }

theorem u23307 : Upper (D 8) (R 8) [320,5,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23307 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23308 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 21 74 184 168 232 168 424), lower := (rows 321 7 21 74 16 32 64 128 256), losses := [] }

theorem u23308 : Upper (D 8) (R 8) [320,5,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23308 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23309 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 21 104 186 170 234 170 426), lower := (rows 321 7 21 104 16 32 64 128 256), losses := [] }

theorem u23309 : Upper (D 8) (R 8) [320,5,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23310 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 21 138 248 232 232 232 488), lower := (rows 321 7 21 138 16 32 64 128 256), losses := [] }

theorem u23310 : Upper (D 8) (R 8) [320,5,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23310 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23311 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 21 168 250 234 234 234 490), lower := (rows 321 7 21 168 16 32 64 128 256), losses := [] }

theorem u23311 : Upper (D 8) (R 8) [320,5,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23312 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 21 200 186 170 234 170 426), lower := (rows 321 7 21 200 16 32 64 128 256), losses := [] }

theorem u23312 : Upper (D 8) (R 8) [320,5,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23313 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 22 41 248 232 232 232 488), lower := (rows 321 7 22 41 16 32 64 128 256), losses := [] }

theorem u23313 : Upper (D 8) (R 8) [320,5,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23313 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23314_9 : Upper (D 8) (R 8) [320,5,18,96,9] 13 :=
  permutation_upper _ _ _ [320,5,10,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17819

theorem m23314_33 : Upper (D 8) (R 8) [320,5,18,96,33] 13 :=
  permutation_upper _ _ _ [320,5,10,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17822

theorem m23314_40 : Upper (D 8) (R 8) [320,5,18,96,40] 13 :=
  permutation_upper _ _ _ [320,5,10,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17827

theorem m23314_129 : Upper (D 8) (R 8) [320,5,18,96,129] 13 :=
  permutation_upper _ _ _ [320,5,10,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17838

theorem m23314_136 : Upper (D 8) (R 8) [320,5,18,96,136] 13 :=
  permutation_upper _ _ _ [320,5,10,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17843

theorem m23314_160 : Upper (D 8) (R 8) [320,5,18,96,160] 13 :=
  permutation_upper _ _ _ [320,5,10,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17849

def r23314 : Route 9 := (fun mask => (mask,id))

def c23314 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23314 : Upper (D 8) (R 8) [320,5,18,96] 13 := by
  apply FastRouting.sound _ _ [320,5,18,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23314 c23314
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23314_9
  · exact m23314_33
  · exact m23314_40
  · exact m23314_129
  · exact m23314_136
  · exact m23314_160

def b23315 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 112, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 22 137 248 232 232 232 488), lower := (rows 321 7 22 137 16 32 64 128 256), losses := [] }

theorem u23315 : Upper (D 8) (R 8) [320,5,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23316_9 : Upper (D 8) (R 8) [320,5,18,160,9] 13 :=
  permutation_upper _ _ _ [320,5,10,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17820

theorem m23316_33 : Upper (D 8) (R 8) [320,5,18,160,33] 13 :=
  permutation_upper _ _ _ [320,5,10,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17823

theorem m23316_40 : Upper (D 8) (R 8) [320,5,18,160,40] 13 :=
  permutation_upper _ _ _ [320,5,10,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17829

theorem m23316_65 : Upper (D 8) (R 8) [320,5,18,160,65] 13 :=
  permutation_upper _ _ _ [320,5,10,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17831

theorem m23316_72 : Upper (D 8) (R 8) [320,5,18,160,72] 13 :=
  permutation_upper _ _ _ [320,5,10,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17834

theorem m23316_96 : Upper (D 8) (R 8) [320,5,18,160,96] 13 :=
  permutation_upper _ _ _ [320,5,10,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17837

theorem m23316_129 : Upper (D 8) (R 8) [320,5,18,160,129] 13 :=
  permutation_upper _ _ _ [320,5,10,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17839

theorem m23316_136 : Upper (D 8) (R 8) [320,5,18,160,136] 13 :=
  permutation_upper _ _ _ [320,5,10,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17845

theorem m23316_160 : Upper (D 8) (R 8) [320,5,18,160,160] 13 :=
  permutation_upper _ _ _ [320,5,10,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17851

theorem m23316_192 : Upper (D 8) (R 8) [320,5,18,160,192] 13 :=
  permutation_upper _ _ _ [320,5,10,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17855

def r23316 : Route 9 := (fun mask => (mask,id))

def c23316 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23316 : Upper (D 8) (R 8) [320,5,18,160] 13 := by
  apply FastRouting.sound _ _ [320,5,18,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23316 c23316
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23316_9
  · exact m23316_33
  · exact m23316_40
  · exact m23316_65
  · exact m23316_72
  · exact m23316_96
  · exact m23316_129
  · exact m23316_136
  · exact m23316_160
  · exact m23316_192

theorem m23317_9 : Upper (D 8) (R 8) [320,5,18,192,9] 13 :=
  permutation_upper _ _ _ [320,5,10,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17821

theorem m23317_33 : Upper (D 8) (R 8) [320,5,18,192,33] 13 :=
  permutation_upper _ _ _ [320,5,10,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17824

theorem m23317_40 : Upper (D 8) (R 8) [320,5,18,192,40] 13 :=
  permutation_upper _ _ _ [320,5,10,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17830

theorem m23317_129 : Upper (D 8) (R 8) [320,5,18,192,129] 13 :=
  permutation_upper _ _ _ [320,5,10,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17840

theorem m23317_136 : Upper (D 8) (R 8) [320,5,18,192,136] 13 :=
  permutation_upper _ _ _ [320,5,10,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17846

theorem m23317_160 : Upper (D 8) (R 8) [320,5,18,192,160] 13 :=
  permutation_upper _ _ _ [320,5,10,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17852

def r23317 : Route 9 := (fun mask => (mask,id))

def c23317 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23317 : Upper (D 8) (R 8) [320,5,18,192] 13 := by
  apply FastRouting.sound _ _ [320,5,18,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23317 c23317
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23317_9
  · exact m23317_33
  · exact m23317_40
  · exact m23317_129
  · exact m23317_136
  · exact m23317_160

def b23318 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 28 41 242 226 226 226 482), lower := (rows 321 7 28 41 16 32 64 128 256), losses := [] }

theorem u23318 : Upper (D 8) (R 8) [320,5,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23319_33 : Upper (D 8) (R 8) [320,5,24,34,33] 13 :=
  permutation_upper _ _ _ [320,5,24,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17856

def r23319 : Route 9 := (fun mask => (mask,id))

def c23319 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23319 : Upper (D 8) (R 8) [320,5,24,34] 13 := by
  apply FastRouting.sound _ _ [320,5,24,34] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23319 c23319
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23319_33
  · exact u17862
  · exact u17863
  · exact u17864
  · exact u17865
  · exact u17866

def b23320 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 28 73 178 162 226 162 418), lower := (rows 321 7 28 73 16 32 64 128 256), losses := [] }

theorem u23320 : Upper (D 8) (R 8) [320,5,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23320 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23321 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 28 74 177 161 225 161 417), lower := (rows 321 7 28 74 16 32 64 128 256), losses := [] }

theorem u23321 : Upper (D 8) (R 8) [320,5,24,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23322 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 28 104 179 163 227 163 419), lower := (rows 321 7 28 104 16 32 64 128 256), losses := [] }

theorem u23322 : Upper (D 8) (R 8) [320,5,24,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23323 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 28 137 242 226 226 226 482), lower := (rows 321 7 28 137 16 32 64 128 256), losses := [] }

theorem u23323 : Upper (D 8) (R 8) [320,5,24,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23324_33 : Upper (D 8) (R 8) [320,5,24,130,33] 13 :=
  permutation_upper _ _ _ [320,5,24,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17859

theorem m23324_65 : Upper (D 8) (R 8) [320,5,24,130,65] 13 :=
  permutation_upper _ _ _ [320,5,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17867

theorem m23324_96 : Upper (D 8) (R 8) [320,5,24,130,96] 13 :=
  permutation_upper _ _ _ [320,5,24,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17872

theorem m23324_129 : Upper (D 8) (R 8) [320,5,24,130,129] 13 :=
  permutation_upper _ _ _ [320,5,24,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17874

def r23324 : Route 9 := (fun mask => (mask,id))

def c23324 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23324 : Upper (D 8) (R 8) [320,5,24,130] 13 := by
  apply FastRouting.sound _ _ [320,5,24,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23324 c23324
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23324_33
  · exact m23324_65
  · exact m23324_96
  · exact m23324_129
  · exact u17877
  · exact u17878

theorem m23325_3 : Upper (D 8) (R 8) [320,5,24,160,3] 13 :=
  permutation_upper _ _ _ [320,5,9,18,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17790

theorem m23325_33 : Upper (D 8) (R 8) [320,5,24,160,33] 13 :=
  permutation_upper _ _ _ [320,5,24,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17860

theorem m23325_34 : Upper (D 8) (R 8) [320,5,24,160,34] 13 :=
  permutation_upper _ _ _ [320,5,24,34,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17865

theorem m23325_65 : Upper (D 8) (R 8) [320,5,24,160,65] 13 :=
  permutation_upper _ _ _ [320,5,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17868

theorem m23325_66 : Upper (D 8) (R 8) [320,5,24,160,66] 13 :=
  permutation_upper _ _ _ [320,5,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17870

theorem m23325_96 : Upper (D 8) (R 8) [320,5,24,160,96] 13 :=
  permutation_upper _ _ _ [320,5,24,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17873

theorem m23325_129 : Upper (D 8) (R 8) [320,5,24,160,129] 13 :=
  permutation_upper _ _ _ [320,5,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17875

theorem m23325_130 : Upper (D 8) (R 8) [320,5,24,160,130] 13 :=
  permutation_upper _ _ _ [320,5,24,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17877

def r23325 : Route 9 := (fun mask => (mask,id))

def c23325 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23325 : Upper (D 8) (R 8) [320,5,24,160] 13 := by
  apply FastRouting.sound _ _ [320,5,24,160] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r23325 c23325
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23325_3
  · exact m23325_33
  · exact m23325_34
  · exact m23325_65
  · exact m23325_66
  · exact m23325_96
  · exact m23325_129
  · exact m23325_130
  · exact u17879
  · exact u17880

def b23326 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 28 200 179 163 227 163 419), lower := (rows 321 7 28 200 16 32 64 128 256), losses := [] }

theorem u23326 : Upper (D 8) (R 8) [320,5,24,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23327 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 26 248 232 232 232 488), lower := (rows 321 7 37 26 16 32 64 128 256), losses := [] }

theorem u23327 : Upper (D 8) (R 8) [320,5,33,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23328 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 37 42 248 248 248 248 504), lower := (rows 321 7 37 42 16 32 64 128 256), losses := [] }

theorem u23328 : Upper (D 8) (R 8) [320,5,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23328 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23329 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 74 184 184 248 184 440), lower := (rows 321 7 37 74 16 32 64 128 256), losses := [] }

theorem u23329 : Upper (D 8) (R 8) [320,5,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23330 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 104 186 186 250 186 442), lower := (rows 321 7 37 104 16 32 64 128 256), losses := [] }

theorem u23330 : Upper (D 8) (R 8) [320,5,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23331 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 138 248 248 248 248 504), lower := (rows 321 7 37 138 16 32 64 128 256), losses := [] }

theorem u23331 : Upper (D 8) (R 8) [320,5,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23332 : PairBound 9 := { available := 250, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 168 250 250 250 250 506), lower := (rows 321 7 37 168 16 32 64 128 256), losses := [] }

theorem u23332 : Upper (D 8) (R 8) [320,5,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23332 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23333 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 37 200 186 186 250 186 442), lower := (rows 321 7 37 200 16 32 64 128 256), losses := [] }

theorem u23333 : Upper (D 8) (R 8) [320,5,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23334 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 38 25 248 232 232 232 488), lower := (rows 321 7 38 25 16 32 64 128 256), losses := [] }

theorem u23334 : Upper (D 8) (R 8) [320,5,34,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23335 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 41 248 248 248 248 504), lower := (rows 321 7 38 41 16 32 64 128 256), losses := [] }

theorem u23335 : Upper (D 8) (R 8) [320,5,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23336_9 : Upper (D 8) (R 8) [320,5,34,48,9] 13 :=
  permutation_upper _ _ _ [320,5,34,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17905

theorem m23336_33 : Upper (D 8) (R 8) [320,5,34,48,33] 13 :=
  permutation_upper _ _ _ [320,5,34,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17911

def r23336 : Route 9 := (fun mask => (mask,id))

def c23336 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23336 : Upper (D 8) (R 8) [320,5,34,48] 13 := by
  apply FastRouting.sound _ _ [320,5,34,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23336 c23336
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23336_9
  · exact m23336_33
  · exact u17917
  · exact u17918
  · exact u17919
  · exact u17920
  · exact u17921
  · exact u17922
  · exact u17923
  · exact u17924

def b23337 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 38 73 184 184 248 184 440), lower := (rows 321 7 38 73 16 32 64 128 256), losses := [] }

theorem u23337 : Upper (D 8) (R 8) [320,5,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23338_9 : Upper (D 8) (R 8) [320,5,34,80,9] 13 :=
  permutation_upper _ _ _ [320,5,34,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17906

theorem m23338_33 : Upper (D 8) (R 8) [320,5,34,80,33] 13 :=
  permutation_upper _ _ _ [320,5,34,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17912

theorem m23338_40 : Upper (D 8) (R 8) [320,5,34,80,40] 13 :=
  permutation_upper _ _ _ [320,5,34,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17919

def r23338 : Route 9 := (fun mask => (mask,id))

def c23338 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23338 : Upper (D 8) (R 8) [320,5,34,80] 13 := by
  apply FastRouting.sound _ _ [320,5,34,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23338 c23338
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23338_9
  · exact m23338_33
  · exact m23338_40
  · exact u17927
  · exact u17928
  · exact u17929

theorem m23339_9 : Upper (D 8) (R 8) [320,5,34,96,9] 13 :=
  permutation_upper _ _ _ [320,5,34,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17907

theorem m23339_33 : Upper (D 8) (R 8) [320,5,34,96,33] 13 :=
  permutation_upper _ _ _ [320,5,34,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17913

theorem m23339_40 : Upper (D 8) (R 8) [320,5,34,96,40] 13 :=
  permutation_upper _ _ _ [320,5,34,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17920

def r23339 : Route 9 := (fun mask => (mask,id))

def c23339 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23339 : Upper (D 8) (R 8) [320,5,34,96] 13 := by
  apply FastRouting.sound _ _ [320,5,34,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23339 c23339
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23339_9
  · exact m23339_33
  · exact m23339_40
  · exact u17930
  · exact u17931
  · exact u17932

#print axioms u23339
end Delivery.IrregularNine14.P08
