import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0298
import IrregularNine14P08C0299
import IrregularNine14P08C0300
import IrregularNine14P08C0301
import IrregularNine14P08C0302
import IrregularNine14P08C0303
import IrregularNine14P08C0304
import IrregularNine14P08C0305
import IrregularNine14P08C0306
import IrregularNine14P08C0307
import IrregularNine14P08C0308
import IrregularNine14P08C0309
import IrregularNine14P08C0310
import IrregularNine14P08C0311
import IrregularNine14P08C0312

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m23760_3 : Upper (D 8) (R 8) [320,36,144,192,3] 13 :=
  permutation_upper _ _ _ [320,5,40,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17999

theorem m23760_9 : Upper (D 8) (R 8) [320,36,144,192,9] 13 :=
  permutation_upper _ _ _ [320,5,192,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18247

theorem m23760_10 : Upper (D 8) (R 8) [320,36,144,192,10] 13 :=
  permutation_upper _ _ _ [320,12,48,192,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18403

theorem m23760_33 : Upper (D 8) (R 8) [320,36,144,192,33] 13 :=
  permutation_upper _ _ _ [320,33,40,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18564

theorem m23760_34 : Upper (D 8) (R 8) [320,36,144,192,34] 13 :=
  permutation_upper _ _ _ [320,36,40,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18659

theorem m23760_40 : Upper (D 8) (R 8) [320,36,144,192,40] 13 :=
  permutation_upper _ _ _ [320,36,136,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18727

def r23760 : Route 9 := (fun mask => (mask,id))

def c23760 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23760 : Upper (D 8) (R 8) [320,36,144,192] 13 := by
  apply FastRouting.sound _ _ [320,36,144,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23760 c23760
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23760_3
  · exact m23760_9
  · exact m23760_10
  · exact m23760_33
  · exact m23760_34
  · exact m23760_40

def b23761 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 74 185 185 249 185 441), lower := (rows 321 38 164 74 16 32 64 128 256), losses := [] }

theorem u23761 : Upper (D 8) (R 8) [320,36,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23761 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23762 : PairBound 9 := { available := 155, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 104 155 187 219 155 411), lower := (rows 321 38 164 104 16 32 64 128 256), losses := [] }

theorem u23762 : Upper (D 8) (R 8) [320,36,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23762 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23763 : PairBound 9 := { available := 123, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 137 123 123 123 251 379), lower := (rows 321 38 164 137 16 32 64 128 256), losses := [] }

theorem u23763 : Upper (D 8) (R 8) [320,36,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23764 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 138 121 121 121 249 377), lower := (rows 321 38 164 138 16 32 64 128 256), losses := [] }

theorem u23764 : Upper (D 8) (R 8) [320,36,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23764 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23765 : PairBound 9 := { available := 91, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 168 91 123 91 219 347), lower := (rows 321 38 164 168 16 32 64 128 256), losses := [] }

theorem u23765 : Upper (D 8) (R 8) [320,36,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23766 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 321 38 164 200 59 59 123 187 315), lower := (rows 321 38 164 200 16 32 64 128 256), losses := [] }

theorem u23766 : Upper (D 8) (R 8) [320,36,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23766 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23767_3 : Upper (D 8) (R 8) [320,36,192,48,3] 13 :=
  permutation_upper _ _ _ [320,5,40,192,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18018

theorem m23767_9 : Upper (D 8) (R 8) [320,36,192,48,9] 13 :=
  permutation_upper _ _ _ [320,5,34,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17924

theorem m23767_10 : Upper (D 8) (R 8) [320,36,192,48,10] 13 :=
  permutation_upper _ _ _ [320,12,34,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18338

theorem m23767_33 : Upper (D 8) (R 8) [320,36,192,48,33] 13 :=
  permutation_upper _ _ _ [320,33,34,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18509

theorem m23767_34 : Upper (D 8) (R 8) [320,36,192,48,34] 13 :=
  permutation_upper _ _ _ [320,36,40,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18643

theorem m23767_40 : Upper (D 8) (R 8) [320,36,192,48,40] 13 :=
  permutation_upper _ _ _ [320,36,34,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18632

theorem m23767_129 : Upper (D 8) (R 8) [320,36,192,48,129] 13 :=
  permutation_upper _ _ _ [320,36,129,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18702

theorem m23767_130 : Upper (D 8) (R 8) [320,36,192,48,130] 13 :=
  permutation_upper _ _ _ [320,36,136,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18727

theorem m23767_136 : Upper (D 8) (R 8) [320,36,192,48,136] 13 :=
  permutation_upper _ _ _ [320,36,130,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18718

theorem m23767_160 : Upper (D 8) (R 8) [320,36,192,48,160] 13 :=
  permutation_upper _ _ _ [320,36,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18745

def r23767 : Route 9 := (fun mask => (mask,id))

def c23767 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23767 : Upper (D 8) (R 8) [320,36,192,48] 13 := by
  apply FastRouting.sound _ _ [320,36,192,48] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23767 c23767
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23767_3
  · exact m23767_9
  · exact m23767_10
  · exact m23767_33
  · exact m23767_34
  · exact m23767_40
  · exact m23767_129
  · exact m23767_130
  · exact m23767_136
  · exact m23767_160

theorem m23768_3 : Upper (D 8) (R 8) [320,36,192,129,3] 13 :=
  permutation_upper _ _ _ [320,5,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18019

theorem m23768_9 : Upper (D 8) (R 8) [320,36,192,129,9] 13 :=
  permutation_upper _ _ _ [320,5,129,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18096

theorem m23768_10 : Upper (D 8) (R 8) [320,36,192,129,10] 13 :=
  permutation_upper _ _ _ [320,12,48,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18384

theorem m23768_33 : Upper (D 8) (R 8) [320,36,192,129,33] 13 :=
  permutation_upper _ _ _ [320,33,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18587

theorem m23768_34 : Upper (D 8) (R 8) [320,36,192,129,34] 13 :=
  permutation_upper _ _ _ [320,36,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18666

theorem m23768_40 : Upper (D 8) (R 8) [320,36,192,129,40] 13 :=
  permutation_upper _ _ _ [320,36,129,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18702

def r23768 : Route 9 := (fun mask => (mask,id))

def c23768 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23768 : Upper (D 8) (R 8) [320,36,192,129] 13 := by
  apply FastRouting.sound _ _ [320,36,192,129] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23768 c23768
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23768_3
  · exact m23768_9
  · exact m23768_10
  · exact m23768_33
  · exact m23768_34
  · exact m23768_40

def b23769 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 38 196 138 57 57 121 185 313), lower := (rows 321 38 196 138 16 32 64 128 256), losses := [] }

theorem u23769 : Upper (D 8) (R 8) [320,36,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23770_3 : Upper (D 8) (R 8) [320,36,192,144,3] 13 :=
  permutation_upper _ _ _ [320,5,40,192,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18020

theorem m23770_9 : Upper (D 8) (R 8) [320,36,192,144,9] 13 :=
  permutation_upper _ _ _ [320,5,130,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18118

theorem m23770_10 : Upper (D 8) (R 8) [320,36,192,144,10] 13 :=
  permutation_upper _ _ _ [320,12,48,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18390

theorem m23770_33 : Upper (D 8) (R 8) [320,36,192,144,33] 13 :=
  permutation_upper _ _ _ [320,33,40,192,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18588

theorem m23770_34 : Upper (D 8) (R 8) [320,36,192,144,34] 13 :=
  permutation_upper _ _ _ [320,36,40,192,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18667

theorem m23770_40 : Upper (D 8) (R 8) [320,36,192,144,40] 13 :=
  permutation_upper _ _ _ [320,36,130,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18718

def r23770 : Route 9 := (fun mask => (mask,id))

def c23770 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23770 : Upper (D 8) (R 8) [320,36,192,144] 13 := by
  apply FastRouting.sound _ _ [320,36,192,144] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23770 c23770
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23770_3
  · exact m23770_9
  · exact m23770_10
  · exact m23770_33
  · exact m23770_34
  · exact m23770_40

theorem m23771_3 : Upper (D 8) (R 8) [320,36,192,160,3] 13 :=
  permutation_upper _ _ _ [320,5,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18021

theorem m23771_9 : Upper (D 8) (R 8) [320,36,192,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18221

theorem m23771_10 : Upper (D 8) (R 8) [320,36,192,160,10] 13 :=
  permutation_upper _ _ _ [320,12,48,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18399

theorem m23771_33 : Upper (D 8) (R 8) [320,36,192,160,33] 13 :=
  permutation_upper _ _ _ [320,33,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18590

theorem m23771_34 : Upper (D 8) (R 8) [320,36,192,160,34] 13 :=
  permutation_upper _ _ _ [320,36,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18668

theorem m23771_40 : Upper (D 8) (R 8) [320,36,192,160,40] 13 :=
  permutation_upper _ _ _ [320,36,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18745

def r23771 : Route 9 := (fun mask => (mask,id))

def c23771 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23771 : Upper (D 8) (R 8) [320,36,192,160] 13 := by
  apply FastRouting.sound _ _ [320,36,192,160] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23771 c23771
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23771_3
  · exact m23771_9
  · exact m23771_10
  · exact m23771_33
  · exact m23771_34
  · exact m23771_40

theorem m23772_5 : Upper (D 8) (R 8) [320,48,66,129,5] 13 :=
  permutation_upper _ _ _ [320,5,72,34,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18046

theorem m23772_9 : Upper (D 8) (R 8) [320,48,66,129,9] 13 :=
  permutation_upper _ _ _ [320,5,129,34,72] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18088

theorem m23772_12 : Upper (D 8) (R 8) [320,48,66,129,12] 13 :=
  permutation_upper _ _ _ [320,12,80,129,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18419

theorem m23772_33 : Upper (D 8) (R 8) [320,48,66,129,33] 13 :=
  permutation_upper _ _ _ [320,33,34,68,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18510

theorem m23772_36 : Upper (D 8) (R 8) [320,48,66,129,36] 13 :=
  permutation_upper _ _ _ [320,36,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18644

theorem m23772_40 : Upper (D 8) (R 8) [320,48,66,129,40] 13 :=
  permutation_upper _ _ _ [320,36,40,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18651

theorem m23772_129 : Upper (D 8) (R 8) [320,48,66,129,129] 13 :=
  permutation_upper _ _ _ [320,36,129,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18705

theorem m23772_132 : Upper (D 8) (R 8) [320,48,66,129,132] 13 :=
  permutation_upper _ _ _ [320,36,136,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18730

theorem m23772_136 : Upper (D 8) (R 8) [320,48,66,129,136] 13 :=
  permutation_upper _ _ _ [320,36,136,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18738

theorem m23772_160 : Upper (D 8) (R 8) [320,48,66,129,160] 13 :=
  permutation_upper _ _ _ [320,36,160,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18746

def r23772 : Route 9 := (fun mask => (mask,id))

def c23772 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23772 : Upper (D 8) (R 8) [320,48,66,129] 13 := by
  apply FastRouting.sound _ _ [320,48,66,129] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r23772 c23772
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23772_5
  · exact m23772_9
  · exact m23772_12
  · exact m23772_33
  · exact m23772_36
  · exact m23772_40
  · exact m23772_129
  · exact m23772_132
  · exact m23772_136
  · exact m23772_160

theorem m23773_9 : Upper (D 8) (R 8) [320,48,66,132,9] 13 :=
  permutation_upper _ _ _ [320,5,136,80,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18160

theorem m23773_33 : Upper (D 8) (R 8) [320,48,66,132,33] 13 :=
  permutation_upper _ _ _ [320,33,34,68,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18511

theorem m23773_40 : Upper (D 8) (R 8) [320,48,66,132,40] 13 :=
  permutation_upper _ _ _ [320,36,40,144,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18660

theorem m23773_129 : Upper (D 8) (R 8) [320,48,66,132,129] 13 :=
  permutation_upper _ _ _ [320,36,129,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18706

theorem m23773_136 : Upper (D 8) (R 8) [320,48,66,132,136] 13 :=
  permutation_upper _ _ _ [320,36,136,144,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18741

theorem m23773_160 : Upper (D 8) (R 8) [320,48,66,132,160] 13 :=
  permutation_upper _ _ _ [320,36,160,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18747

def r23773 : Route 9 := (fun mask => (mask,id))

def c23773 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23773 : Upper (D 8) (R 8) [320,48,66,132] 13 := by
  apply FastRouting.sound _ _ [320,48,66,132] 13 (by decide) (choices 2) [9,33,40,129,136,160] r23773 c23773
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23773_9
  · exact m23773_33
  · exact m23773_40
  · exact m23773_129
  · exact m23773_136
  · exact m23773_160

theorem m23774_5 : Upper (D 8) (R 8) [320,48,66,160,5] 13 :=
  permutation_upper _ _ _ [320,5,72,34,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18047

theorem m23774_9 : Upper (D 8) (R 8) [320,48,66,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,34,72] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18206

theorem m23774_12 : Upper (D 8) (R 8) [320,48,66,160,12] 13 :=
  permutation_upper _ _ _ [320,12,80,160,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18427

theorem m23774_33 : Upper (D 8) (R 8) [320,48,66,160,33] 13 :=
  permutation_upper _ _ _ [320,33,34,68,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18512

theorem m23774_36 : Upper (D 8) (R 8) [320,48,66,160,36] 13 :=
  permutation_upper _ _ _ [320,36,40,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18645

theorem m23774_40 : Upper (D 8) (R 8) [320,48,66,160,40] 13 :=
  permutation_upper _ _ _ [320,36,40,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18662

theorem m23774_129 : Upper (D 8) (R 8) [320,48,66,160,129] 13 :=
  permutation_upper _ _ _ [320,36,129,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18707

theorem m23774_132 : Upper (D 8) (R 8) [320,48,66,160,132] 13 :=
  permutation_upper _ _ _ [320,36,136,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18731

theorem m23774_136 : Upper (D 8) (R 8) [320,48,66,160,136] 13 :=
  permutation_upper _ _ _ [320,36,136,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18743

theorem m23774_160 : Upper (D 8) (R 8) [320,48,66,160,160] 13 :=
  permutation_upper _ _ _ [320,36,160,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18748

def r23774 : Route 9 := (fun mask => (mask,id))

def c23774 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23774 : Upper (D 8) (R 8) [320,48,66,160] 13 := by
  apply FastRouting.sound _ _ [320,48,66,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r23774 c23774
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23774_5
  · exact m23774_9
  · exact m23774_12
  · exact m23774_33
  · exact m23774_36
  · exact m23774_40
  · exact m23774_129
  · exact m23774_132
  · exact m23774_136
  · exact m23774_160

theorem m23775_3 : Upper (D 8) (R 8) [320,48,72,129,3] 13 :=
  permutation_upper _ _ _ [320,5,34,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17927

theorem m23775_5 : Upper (D 8) (R 8) [320,48,72,129,5] 13 :=
  permutation_upper _ _ _ [320,5,72,129,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18050

theorem m23775_6 : Upper (D 8) (R 8) [320,48,72,129,6] 13 :=
  permutation_upper _ _ _ [320,12,34,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18343

theorem m23775_33 : Upper (D 8) (R 8) [320,48,72,129,33] 13 :=
  permutation_upper _ _ _ [320,33,34,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18513

theorem m23775_34 : Upper (D 8) (R 8) [320,48,72,129,34] 13 :=
  permutation_upper _ _ _ [320,36,34,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18633

theorem m23775_36 : Upper (D 8) (R 8) [320,48,72,129,36] 13 :=
  permutation_upper _ _ _ [320,36,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18646

theorem m23775_129 : Upper (D 8) (R 8) [320,48,72,129,129] 13 :=
  permutation_upper _ _ _ [320,36,129,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18708

theorem m23775_130 : Upper (D 8) (R 8) [320,48,72,129,130] 13 :=
  permutation_upper _ _ _ [320,36,130,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18719

theorem m23775_132 : Upper (D 8) (R 8) [320,48,72,129,132] 13 :=
  permutation_upper _ _ _ [320,36,136,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18732

theorem m23775_160 : Upper (D 8) (R 8) [320,48,72,129,160] 13 :=
  permutation_upper _ _ _ [320,36,160,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18749

def r23775 : Route 9 := (fun mask => (mask,id))

def c23775 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 257 => 8 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23775 : Upper (D 8) (R 8) [320,48,72,129] 13 := by
  apply FastRouting.sound _ _ [320,48,72,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160] r23775 c23775
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23775_3
  · exact m23775_5
  · exact m23775_6
  · exact m23775_33
  · exact m23775_34
  · exact m23775_36
  · exact m23775_129
  · exact m23775_130
  · exact m23775_132
  · exact m23775_160

theorem m23776_5 : Upper (D 8) (R 8) [320,48,72,130,5] 13 :=
  permutation_upper _ _ _ [320,5,72,144,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18057

theorem m23776_33 : Upper (D 8) (R 8) [320,48,72,130,33] 13 :=
  permutation_upper _ _ _ [320,33,34,80,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18514

theorem m23776_36 : Upper (D 8) (R 8) [320,48,72,130,36] 13 :=
  permutation_upper _ _ _ [320,36,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18647

theorem m23776_129 : Upper (D 8) (R 8) [320,48,72,130,129] 13 :=
  permutation_upper _ _ _ [320,36,129,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18709

theorem m23776_132 : Upper (D 8) (R 8) [320,48,72,130,132] 13 :=
  permutation_upper _ _ _ [320,36,136,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18733

theorem m23776_160 : Upper (D 8) (R 8) [320,48,72,130,160] 13 :=
  permutation_upper _ _ _ [320,36,160,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18750

def r23776 : Route 9 := (fun mask => (mask,id))

def c23776 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23776 : Upper (D 8) (R 8) [320,48,72,130] 13 := by
  apply FastRouting.sound _ _ [320,48,72,130] 13 (by decide) (choices 2) [5,33,36,129,132,160] r23776 c23776
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23776_5
  · exact m23776_33
  · exact m23776_36
  · exact m23776_129
  · exact m23776_132
  · exact m23776_160

theorem m23777_3 : Upper (D 8) (R 8) [320,48,72,160,3] 13 :=
  permutation_upper _ _ _ [320,5,34,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17929

theorem m23777_5 : Upper (D 8) (R 8) [320,48,72,160,5] 13 :=
  permutation_upper _ _ _ [320,5,72,160,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18059

theorem m23777_6 : Upper (D 8) (R 8) [320,48,72,160,6] 13 :=
  permutation_upper _ _ _ [320,12,34,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18344

theorem m23777_33 : Upper (D 8) (R 8) [320,48,72,160,33] 13 :=
  permutation_upper _ _ _ [320,33,34,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18515

theorem m23777_34 : Upper (D 8) (R 8) [320,48,72,160,34] 13 :=
  permutation_upper _ _ _ [320,36,34,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18634

theorem m23777_36 : Upper (D 8) (R 8) [320,48,72,160,36] 13 :=
  permutation_upper _ _ _ [320,36,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18648

theorem m23777_129 : Upper (D 8) (R 8) [320,48,72,160,129] 13 :=
  permutation_upper _ _ _ [320,36,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18711

theorem m23777_130 : Upper (D 8) (R 8) [320,48,72,160,130] 13 :=
  permutation_upper _ _ _ [320,36,130,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18721

theorem m23777_132 : Upper (D 8) (R 8) [320,48,72,160,132] 13 :=
  permutation_upper _ _ _ [320,36,136,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18734

theorem m23777_160 : Upper (D 8) (R 8) [320,48,72,160,160] 13 :=
  permutation_upper _ _ _ [320,36,160,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18751

def r23777 : Route 9 := (fun mask => (mask,id))

def c23777 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 257 => 8 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23777 : Upper (D 8) (R 8) [320,48,72,160] 13 := by
  apply FastRouting.sound _ _ [320,48,72,160] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160] r23777 c23777
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23777_3
  · exact m23777_5
  · exact m23777_6
  · exact m23777_33
  · exact m23777_34
  · exact m23777_36
  · exact m23777_129
  · exact m23777_130
  · exact m23777_132
  · exact m23777_160

theorem m23778_3 : Upper (D 8) (R 8) [320,48,96,129,3] 13 :=
  permutation_upper _ _ _ [320,5,34,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17930

theorem m23778_5 : Upper (D 8) (R 8) [320,48,96,129,5] 13 :=
  permutation_upper _ _ _ [320,5,96,34,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18074

theorem m23778_6 : Upper (D 8) (R 8) [320,48,96,129,6] 13 :=
  permutation_upper _ _ _ [320,12,34,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18346

theorem m23778_9 : Upper (D 8) (R 8) [320,48,96,129,9] 13 :=
  permutation_upper _ _ _ [320,5,129,34,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18089

theorem m23778_10 : Upper (D 8) (R 8) [320,48,96,129,10] 13 :=
  permutation_upper _ _ _ [320,12,34,129,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18350

theorem m23778_12 : Upper (D 8) (R 8) [320,48,96,129,12] 13 :=
  permutation_upper _ _ _ [320,12,96,129,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18432

theorem m23778_33 : Upper (D 8) (R 8) [320,48,96,129,33] 13 :=
  permutation_upper _ _ _ [320,33,34,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18516

theorem m23778_34 : Upper (D 8) (R 8) [320,48,96,129,34] 13 :=
  permutation_upper _ _ _ [320,36,34,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18635

theorem m23778_36 : Upper (D 8) (R 8) [320,48,96,129,36] 13 :=
  permutation_upper _ _ _ [320,36,40,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18649

theorem m23778_40 : Upper (D 8) (R 8) [320,48,96,129,40] 13 :=
  permutation_upper _ _ _ [320,36,40,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18652

theorem m23778_129 : Upper (D 8) (R 8) [320,48,96,129,129] 13 :=
  permutation_upper _ _ _ [320,36,129,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18712

theorem m23778_130 : Upper (D 8) (R 8) [320,48,96,129,130] 13 :=
  permutation_upper _ _ _ [320,36,130,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18722

theorem m23778_132 : Upper (D 8) (R 8) [320,48,96,129,132] 13 :=
  permutation_upper _ _ _ [320,36,136,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18735

theorem m23778_136 : Upper (D 8) (R 8) [320,48,96,129,136] 13 :=
  permutation_upper _ _ _ [320,36,136,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18739

theorem m23778_160 : Upper (D 8) (R 8) [320,48,96,129,160] 13 :=
  permutation_upper _ _ _ [320,36,160,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18752

def r23778 : Route 9 := (fun mask => (mask,id))

def c23778 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 257 => 8 | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23778 : Upper (D 8) (R 8) [320,48,96,129] 13 := by
  apply FastRouting.sound _ _ [320,48,96,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,129,130,132,136,160] r23778 c23778
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23778_3
  · exact m23778_5
  · exact m23778_6
  · exact m23778_9
  · exact m23778_10
  · exact m23778_12
  · exact m23778_33
  · exact m23778_34
  · exact m23778_36
  · exact m23778_40
  · exact m23778_129
  · exact m23778_130
  · exact m23778_132
  · exact m23778_136
  · exact m23778_160

theorem m23779_5 : Upper (D 8) (R 8) [320,48,96,130,5] 13 :=
  permutation_upper _ _ _ [320,5,96,34,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18075

theorem m23779_9 : Upper (D 8) (R 8) [320,48,96,130,9] 13 :=
  permutation_upper _ _ _ [320,5,136,34,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18141

theorem m23779_12 : Upper (D 8) (R 8) [320,48,96,130,12] 13 :=
  permutation_upper _ _ _ [320,12,96,144,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18440

theorem m23779_33 : Upper (D 8) (R 8) [320,48,96,130,33] 13 :=
  permutation_upper _ _ _ [320,33,34,96,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18517

theorem m23779_36 : Upper (D 8) (R 8) [320,48,96,130,36] 13 :=
  permutation_upper _ _ _ [320,36,40,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18650

theorem m23779_40 : Upper (D 8) (R 8) [320,48,96,130,40] 13 :=
  permutation_upper _ _ _ [320,36,40,130,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18656

theorem m23779_129 : Upper (D 8) (R 8) [320,48,96,130,129] 13 :=
  permutation_upper _ _ _ [320,36,129,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18713

theorem m23779_132 : Upper (D 8) (R 8) [320,48,96,130,132] 13 :=
  permutation_upper _ _ _ [320,36,136,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18736

theorem m23779_136 : Upper (D 8) (R 8) [320,48,96,130,136] 13 :=
  permutation_upper _ _ _ [320,36,136,130,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18740

theorem m23779_160 : Upper (D 8) (R 8) [320,48,96,130,160] 13 :=
  permutation_upper _ _ _ [320,36,160,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18753

def r23779 : Route 9 := (fun mask => (mask,id))

def c23779 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23779 : Upper (D 8) (R 8) [320,48,96,130] 13 := by
  apply FastRouting.sound _ _ [320,48,96,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r23779 c23779
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23779_5
  · exact m23779_9
  · exact m23779_12
  · exact m23779_33
  · exact m23779_36
  · exact m23779_40
  · exact m23779_129
  · exact m23779_132
  · exact m23779_136
  · exact m23779_160

theorem m23780_3 : Upper (D 8) (R 8) [320,48,96,132,3] 13 :=
  permutation_upper _ _ _ [320,5,34,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17931

theorem m23780_9 : Upper (D 8) (R 8) [320,48,96,132,9] 13 :=
  permutation_upper _ _ _ [320,5,136,96,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18165

theorem m23780_10 : Upper (D 8) (R 8) [320,48,96,132,10] 13 :=
  permutation_upper _ _ _ [320,12,34,144,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18356

theorem m23780_33 : Upper (D 8) (R 8) [320,48,96,132,33] 13 :=
  permutation_upper _ _ _ [320,33,34,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18518

theorem m23780_34 : Upper (D 8) (R 8) [320,48,96,132,34] 13 :=
  permutation_upper _ _ _ [320,36,34,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18636

theorem m23780_40 : Upper (D 8) (R 8) [320,48,96,132,40] 13 :=
  permutation_upper _ _ _ [320,36,40,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18661

theorem m23780_129 : Upper (D 8) (R 8) [320,48,96,132,129] 13 :=
  permutation_upper _ _ _ [320,36,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18714

theorem m23780_130 : Upper (D 8) (R 8) [320,48,96,132,130] 13 :=
  permutation_upper _ _ _ [320,36,130,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18723

theorem m23780_136 : Upper (D 8) (R 8) [320,48,96,132,136] 13 :=
  permutation_upper _ _ _ [320,36,136,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18742

theorem m23780_160 : Upper (D 8) (R 8) [320,48,96,132,160] 13 :=
  permutation_upper _ _ _ [320,36,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18754

def r23780 : Route 9 := (fun mask => (mask,id))

def c23780 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23780 : Upper (D 8) (R 8) [320,48,96,132] 13 := by
  apply FastRouting.sound _ _ [320,48,96,132] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23780 c23780
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23780_3
  · exact m23780_9
  · exact m23780_10
  · exact m23780_33
  · exact m23780_34
  · exact m23780_40
  · exact m23780_129
  · exact m23780_130
  · exact m23780_136
  · exact m23780_160

theorem m23781_3 : Upper (D 8) (R 8) [320,48,96,160,3] 13 :=
  permutation_upper _ _ _ [320,5,34,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17932

theorem m23781_5 : Upper (D 8) (R 8) [320,48,96,160,5] 13 :=
  permutation_upper _ _ _ [320,5,96,34,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18076

theorem m23781_6 : Upper (D 8) (R 8) [320,48,96,160,6] 13 :=
  permutation_upper _ _ _ [320,12,34,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18347

theorem m23781_9 : Upper (D 8) (R 8) [320,48,96,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,34,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18207

theorem m23781_10 : Upper (D 8) (R 8) [320,48,96,160,10] 13 :=
  permutation_upper _ _ _ [320,12,34,160,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18361

theorem m23781_12 : Upper (D 8) (R 8) [320,48,96,160,12] 13 :=
  permutation_upper _ _ _ [320,12,96,160,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18445

theorem m23781_129 : Upper (D 8) (R 8) [320,48,96,160,129] 13 :=
  permutation_upper _ _ _ [320,36,129,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18715

theorem m23781_130 : Upper (D 8) (R 8) [320,48,96,160,130] 13 :=
  permutation_upper _ _ _ [320,36,130,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18724

theorem m23781_132 : Upper (D 8) (R 8) [320,48,96,160,132] 13 :=
  permutation_upper _ _ _ [320,36,136,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18737

theorem m23781_136 : Upper (D 8) (R 8) [320,48,96,160,136] 13 :=
  permutation_upper _ _ _ [320,36,136,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18744

def r23781 : Route 9 := (fun mask => (mask,id))

def c23781 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23781 : Upper (D 8) (R 8) [320,48,96,160] 13 := by
  apply FastRouting.sound _ _ [320,48,96,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136] r23781 c23781
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23781_3
  · exact m23781_5
  · exact m23781_6
  · exact m23781_9
  · exact m23781_10
  · exact m23781_12
  · exact m23781_129
  · exact m23781_130
  · exact m23781_132
  · exact m23781_136

theorem m23782_5 : Upper (D 8) (R 8) [320,48,129,130,5] 13 :=
  permutation_upper _ _ _ [320,5,129,34,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18090

theorem m23782_9 : Upper (D 8) (R 8) [320,48,129,130,9] 13 :=
  permutation_upper _ _ _ [320,5,136,34,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18142

theorem m23782_12 : Upper (D 8) (R 8) [320,48,129,130,12] 13 :=
  permutation_upper _ _ _ [320,12,129,144,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18455

theorem m23782_33 : Upper (D 8) (R 8) [320,48,129,130,33] 13 :=
  permutation_upper _ _ _ [320,33,34,129,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18519

theorem m23782_36 : Upper (D 8) (R 8) [320,48,129,130,36] 13 :=
  permutation_upper _ _ _ [320,36,40,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18653

theorem m23782_40 : Upper (D 8) (R 8) [320,48,129,130,40] 13 :=
  permutation_upper _ _ _ [320,36,40,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18657

theorem m23782_65 : Upper (D 8) (R 8) [320,48,129,130,65] 13 :=
  permutation_upper _ _ _ [320,36,65,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18672

theorem m23782_68 : Upper (D 8) (R 8) [320,48,129,130,68] 13 :=
  permutation_upper _ _ _ [320,36,72,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18682

theorem m23782_72 : Upper (D 8) (R 8) [320,48,129,130,72] 13 :=
  permutation_upper _ _ _ [320,36,72,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18684

theorem m23782_96 : Upper (D 8) (R 8) [320,48,129,130,96] 13 :=
  permutation_upper _ _ _ [320,36,96,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18695

def r23782 : Route 9 := (fun mask => (mask,id))

def c23782 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u23782 : Upper (D 8) (R 8) [320,48,129,130] 13 := by
  apply FastRouting.sound _ _ [320,48,129,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r23782 c23782
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23782_5
  · exact m23782_9
  · exact m23782_12
  · exact m23782_33
  · exact m23782_36
  · exact m23782_40
  · exact m23782_65
  · exact m23782_68
  · exact m23782_72
  · exact m23782_96

theorem m23783_3 : Upper (D 8) (R 8) [320,48,129,160,3] 13 :=
  permutation_upper _ _ _ [320,5,34,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17934

theorem m23783_5 : Upper (D 8) (R 8) [320,48,129,160,5] 13 :=
  permutation_upper _ _ _ [320,5,129,34,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18091

theorem m23783_6 : Upper (D 8) (R 8) [320,48,129,160,6] 13 :=
  permutation_upper _ _ _ [320,12,34,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18352

theorem m23783_9 : Upper (D 8) (R 8) [320,48,129,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,34,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18208

theorem m23783_10 : Upper (D 8) (R 8) [320,48,129,160,10] 13 :=
  permutation_upper _ _ _ [320,12,34,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18362

theorem m23783_12 : Upper (D 8) (R 8) [320,48,129,160,12] 13 :=
  permutation_upper _ _ _ [320,12,129,160,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18459

theorem m23783_33 : Upper (D 8) (R 8) [320,48,129,160,33] 13 :=
  permutation_upper _ _ _ [320,33,34,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18520

theorem m23783_34 : Upper (D 8) (R 8) [320,48,129,160,34] 13 :=
  permutation_upper _ _ _ [320,36,34,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18637

theorem m23783_36 : Upper (D 8) (R 8) [320,48,129,160,36] 13 :=
  permutation_upper _ _ _ [320,36,40,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18654

theorem m23783_40 : Upper (D 8) (R 8) [320,48,129,160,40] 13 :=
  permutation_upper _ _ _ [320,36,40,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18663

theorem m23783_65 : Upper (D 8) (R 8) [320,48,129,160,65] 13 :=
  permutation_upper _ _ _ [320,36,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18673

theorem m23783_66 : Upper (D 8) (R 8) [320,48,129,160,66] 13 :=
  permutation_upper _ _ _ [320,36,66,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18677

theorem m23783_68 : Upper (D 8) (R 8) [320,48,129,160,68] 13 :=
  permutation_upper _ _ _ [320,36,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18683

theorem m23783_72 : Upper (D 8) (R 8) [320,48,129,160,72] 13 :=
  permutation_upper _ _ _ [320,36,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18689

theorem m23783_96 : Upper (D 8) (R 8) [320,48,129,160,96] 13 :=
  permutation_upper _ _ _ [320,36,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18696

def r23783 : Route 9 := (fun mask => (mask,id))

def c23783 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u23783 : Upper (D 8) (R 8) [320,48,129,160] 13 := by
  apply FastRouting.sound _ _ [320,48,129,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r23783 c23783
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23783_3
  · exact m23783_5
  · exact m23783_6
  · exact m23783_9
  · exact m23783_10
  · exact m23783_12
  · exact m23783_33
  · exact m23783_34
  · exact m23783_36
  · exact m23783_40
  · exact m23783_65
  · exact m23783_66
  · exact m23783_68
  · exact m23783_72
  · exact m23783_96

theorem m23784_3 : Upper (D 8) (R 8) [320,48,129,192,3] 13 :=
  permutation_upper _ _ _ [320,5,34,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17935

theorem m23784_5 : Upper (D 8) (R 8) [320,48,129,192,5] 13 :=
  permutation_upper _ _ _ [320,5,129,34,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18092

theorem m23784_6 : Upper (D 8) (R 8) [320,48,129,192,6] 13 :=
  permutation_upper _ _ _ [320,12,34,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18353

theorem m23784_9 : Upper (D 8) (R 8) [320,48,129,192,9] 13 :=
  permutation_upper _ _ _ [320,5,192,34,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18243

theorem m23784_10 : Upper (D 8) (R 8) [320,48,129,192,10] 13 :=
  permutation_upper _ _ _ [320,12,34,192,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18366

theorem m23784_12 : Upper (D 8) (R 8) [320,48,129,192,12] 13 :=
  permutation_upper _ _ _ [320,12,129,192,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18463

theorem m23784_33 : Upper (D 8) (R 8) [320,48,129,192,33] 13 :=
  permutation_upper _ _ _ [320,33,34,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18521

theorem m23784_34 : Upper (D 8) (R 8) [320,48,129,192,34] 13 :=
  permutation_upper _ _ _ [320,36,34,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18638

theorem m23784_36 : Upper (D 8) (R 8) [320,48,129,192,36] 13 :=
  permutation_upper _ _ _ [320,36,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18655

theorem m23784_40 : Upper (D 8) (R 8) [320,48,129,192,40] 13 :=
  permutation_upper _ _ _ [320,36,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18666

def r23784 : Route 9 := (fun mask => (mask,id))

def c23784 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23784 : Upper (D 8) (R 8) [320,48,129,192] 13 := by
  apply FastRouting.sound _ _ [320,48,129,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r23784 c23784
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23784_3
  · exact m23784_5
  · exact m23784_6
  · exact m23784_9
  · exact m23784_10
  · exact m23784_12
  · exact m23784_33
  · exact m23784_34
  · exact m23784_36
  · exact m23784_40

theorem m23785_5 : Upper (D 8) (R 8) [320,48,130,160,5] 13 :=
  permutation_upper _ _ _ [320,5,136,34,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18143

theorem m23785_9 : Upper (D 8) (R 8) [320,48,130,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,34,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18209

theorem m23785_12 : Upper (D 8) (R 8) [320,48,130,160,12] 13 :=
  permutation_upper _ _ _ [320,12,144,160,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18470

theorem m23785_33 : Upper (D 8) (R 8) [320,48,130,160,33] 13 :=
  permutation_upper _ _ _ [320,33,34,132,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18522

theorem m23785_36 : Upper (D 8) (R 8) [320,48,130,160,36] 13 :=
  permutation_upper _ _ _ [320,36,40,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18658

theorem m23785_40 : Upper (D 8) (R 8) [320,48,130,160,40] 13 :=
  permutation_upper _ _ _ [320,36,40,160,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18664

theorem m23785_65 : Upper (D 8) (R 8) [320,48,130,160,65] 13 :=
  permutation_upper _ _ _ [320,36,65,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18674

theorem m23785_68 : Upper (D 8) (R 8) [320,48,130,160,68] 13 :=
  permutation_upper _ _ _ [320,36,72,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18685

theorem m23785_72 : Upper (D 8) (R 8) [320,48,130,160,72] 13 :=
  permutation_upper _ _ _ [320,36,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18690

theorem m23785_96 : Upper (D 8) (R 8) [320,48,130,160,96] 13 :=
  permutation_upper _ _ _ [320,36,96,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18697

def r23785 : Route 9 := (fun mask => (mask,id))

def c23785 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u23785 : Upper (D 8) (R 8) [320,48,130,160] 13 := by
  apply FastRouting.sound _ _ [320,48,130,160] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r23785 c23785
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23785_5
  · exact m23785_9
  · exact m23785_12
  · exact m23785_33
  · exact m23785_36
  · exact m23785_40
  · exact m23785_65
  · exact m23785_68
  · exact m23785_72
  · exact m23785_96

theorem m23786_5 : Upper (D 8) (R 8) [320,48,130,192,5] 13 :=
  permutation_upper _ _ _ [320,5,136,34,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18144

theorem m23786_9 : Upper (D 8) (R 8) [320,48,130,192,9] 13 :=
  permutation_upper _ _ _ [320,5,192,34,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18244

theorem m23786_12 : Upper (D 8) (R 8) [320,48,130,192,12] 13 :=
  permutation_upper _ _ _ [320,12,144,192,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18474

theorem m23786_33 : Upper (D 8) (R 8) [320,48,130,192,33] 13 :=
  permutation_upper _ _ _ [320,33,34,132,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18523

theorem m23786_36 : Upper (D 8) (R 8) [320,48,130,192,36] 13 :=
  permutation_upper _ _ _ [320,36,40,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18659

theorem m23786_40 : Upper (D 8) (R 8) [320,48,130,192,40] 13 :=
  permutation_upper _ _ _ [320,36,40,192,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18667

def r23786 : Route 9 := (fun mask => (mask,id))

def c23786 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23786 : Upper (D 8) (R 8) [320,48,130,192] 13 := by
  apply FastRouting.sound _ _ [320,48,130,192] 13 (by decide) (choices 2) [5,9,12,33,36,40] r23786 c23786
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23786_5
  · exact m23786_9
  · exact m23786_12
  · exact m23786_33
  · exact m23786_36
  · exact m23786_40

theorem m23787_3 : Upper (D 8) (R 8) [320,48,160,192,3] 13 :=
  permutation_upper _ _ _ [320,5,34,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17940

theorem m23787_5 : Upper (D 8) (R 8) [320,48,160,192,5] 13 :=
  permutation_upper _ _ _ [320,5,160,34,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18211

theorem m23787_6 : Upper (D 8) (R 8) [320,48,160,192,6] 13 :=
  permutation_upper _ _ _ [320,12,34,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18364

theorem m23787_9 : Upper (D 8) (R 8) [320,48,160,192,9] 13 :=
  permutation_upper _ _ _ [320,5,192,34,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18245

theorem m23787_10 : Upper (D 8) (R 8) [320,48,160,192,10] 13 :=
  permutation_upper _ _ _ [320,12,34,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18367

theorem m23787_12 : Upper (D 8) (R 8) [320,48,160,192,12] 13 :=
  permutation_upper _ _ _ [320,12,160,192,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18480

theorem m23787_33 : Upper (D 8) (R 8) [320,48,160,192,33] 13 :=
  permutation_upper _ _ _ [320,33,34,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18524

theorem m23787_34 : Upper (D 8) (R 8) [320,48,160,192,34] 13 :=
  permutation_upper _ _ _ [320,36,34,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18639

theorem m23787_36 : Upper (D 8) (R 8) [320,48,160,192,36] 13 :=
  permutation_upper _ _ _ [320,36,40,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18665

theorem m23787_40 : Upper (D 8) (R 8) [320,48,160,192,40] 13 :=
  permutation_upper _ _ _ [320,36,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18668

def r23787 : Route 9 := (fun mask => (mask,id))

def c23787 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23787 : Upper (D 8) (R 8) [320,48,160,192] 13 := by
  apply FastRouting.sound _ _ [320,48,160,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r23787 c23787
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23787_3
  · exact m23787_5
  · exact m23787_6
  · exact m23787_9
  · exact m23787_10
  · exact m23787_12
  · exact m23787_33
  · exact m23787_34
  · exact m23787_36
  · exact m23787_40

def b23788 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 188, targets := 64 }], pairs := [(2,6)], upper := (rows 321 67 133 138 60 60 124 188 316), lower := (rows 321 67 133 138 16 32 64 128 256), losses := [] }

theorem u23788 : Upper (D 8) (R 8) [320,65,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23789 : PairBound 9 := { available := 62, camps := [{ cop := 1, region := 188, targets := 64 }], pairs := [(2,6)], upper := (rows 321 67 133 168 62 62 126 190 318), lower := (rows 321 67 133 168 16 32 64 128 256), losses := [] }

theorem u23789 : Upper (D 8) (R 8) [320,65,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23790 : PairBound 9 := { available := 61, camps := [{ cop := 1, region := 188, targets := 64 }], pairs := [(2,6)], upper := (rows 321 67 134 168 61 61 125 189 317), lower := (rows 321 67 134 168 16 32 64 128 256), losses := [] }

theorem u23790 : Upper (D 8) (R 8) [320,65,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23791 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 321 70 133 137 58 58 122 186 314), lower := (rows 321 70 133 137 16 32 64 128 256), losses := [] }

theorem u23791 : Upper (D 8) (R 8) [320,68,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23792 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 70 133 138 57 57 121 185 313), lower := (rows 321 70 133 138 16 32 64 128 256), losses := [] }

theorem u23792 : Upper (D 8) (R 8) [320,68,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23793_3 : Upper (D 8) (R 8) [320,68,129,144,3] 13 :=
  permutation_upper _ _ _ [320,5,72,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18051

theorem m23793_9 : Upper (D 8) (R 8) [320,68,129,144,9] 13 :=
  permutation_upper _ _ _ [320,5,130,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18119

theorem m23793_10 : Upper (D 8) (R 8) [320,68,129,144,10] 13 :=
  permutation_upper _ _ _ [320,12,80,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18424

theorem m23793_33 : Upper (D 8) (R 8) [320,68,129,144,33] 13 :=
  permutation_upper _ _ _ [320,33,72,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18602

theorem m23793_34 : Upper (D 8) (R 8) [320,68,129,144,34] 13 :=
  permutation_upper _ _ _ [320,36,72,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18682

theorem m23793_40 : Upper (D 8) (R 8) [320,68,129,144,40] 13 :=
  permutation_upper _ _ _ [320,36,130,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18719

def r23793 : Route 9 := (fun mask => (mask,id))

def c23793 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23793 : Upper (D 8) (R 8) [320,68,129,144] 13 := by
  apply FastRouting.sound _ _ [320,68,129,144] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23793 c23793
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23793_3
  · exact m23793_9
  · exact m23793_10
  · exact m23793_33
  · exact m23793_34
  · exact m23793_40

theorem m23794_3 : Upper (D 8) (R 8) [320,68,129,160,3] 13 :=
  permutation_upper _ _ _ [320,5,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18052

theorem m23794_9 : Upper (D 8) (R 8) [320,68,129,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18226

theorem m23794_10 : Upper (D 8) (R 8) [320,68,129,160,10] 13 :=
  permutation_upper _ _ _ [320,12,80,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18428

theorem m23794_33 : Upper (D 8) (R 8) [320,68,129,160,33] 13 :=
  permutation_upper _ _ _ [320,33,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18604

theorem m23794_34 : Upper (D 8) (R 8) [320,68,129,160,34] 13 :=
  permutation_upper _ _ _ [320,36,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18683

theorem m23794_40 : Upper (D 8) (R 8) [320,68,129,160,40] 13 :=
  permutation_upper _ _ _ [320,36,160,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18749

def r23794 : Route 9 := (fun mask => (mask,id))

def c23794 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23794 : Upper (D 8) (R 8) [320,68,129,160] 13 := by
  apply FastRouting.sound _ _ [320,68,129,160] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23794 c23794
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23794_3
  · exact m23794_9
  · exact m23794_10
  · exact m23794_33
  · exact m23794_34
  · exact m23794_40

def b23795 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 70 134 137 57 57 121 185 313), lower := (rows 321 70 134 137 16 32 64 128 256), losses := [] }

theorem u23795 : Upper (D 8) (R 8) [320,68,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23796 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 321 70 134 168 57 57 121 185 313), lower := (rows 321 70 134 168 16 32 64 128 256), losses := [] }

theorem u23796 : Upper (D 8) (R 8) [320,68,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23797 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 70 140 137 51 51 115 179 307), lower := (rows 321 70 140 137 16 32 64 128 256), losses := [] }

theorem u23797 : Upper (D 8) (R 8) [320,68,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23798 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 70 140 138 49 49 113 177 305), lower := (rows 321 70 140 138 16 32 64 128 256), losses := [] }

theorem u23798 : Upper (D 8) (R 8) [320,68,136,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23799 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 70 140 152 51 35 99 163 291), lower := (rows 321 70 140 152 16 32 64 128 256), losses := [] }

theorem u23799 : Upper (D 8) (R 8) [320,68,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23800 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 70 140 168 51 51 115 179 307), lower := (rows 321 70 140 168 16 32 64 128 256), losses := [] }

theorem u23800 : Upper (D 8) (R 8) [320,68,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23801_3 : Upper (D 8) (R 8) [320,68,144,129,3] 13 :=
  permutation_upper _ _ _ [320,5,72,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18054

theorem m23801_9 : Upper (D 8) (R 8) [320,68,144,129,9] 13 :=
  permutation_upper _ _ _ [320,5,129,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18099

theorem m23801_10 : Upper (D 8) (R 8) [320,68,144,129,10] 13 :=
  permutation_upper _ _ _ [320,12,80,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18421

theorem m23801_33 : Upper (D 8) (R 8) [320,68,144,129,33] 13 :=
  permutation_upper _ _ _ [320,33,72,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18605

theorem m23801_34 : Upper (D 8) (R 8) [320,68,144,129,34] 13 :=
  permutation_upper _ _ _ [320,36,72,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18684

theorem m23801_40 : Upper (D 8) (R 8) [320,68,144,129,40] 13 :=
  permutation_upper _ _ _ [320,36,129,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18709

def r23801 : Route 9 := (fun mask => (mask,id))

def c23801 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23801 : Upper (D 8) (R 8) [320,68,144,129] 13 := by
  apply FastRouting.sound _ _ [320,68,144,129] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23801 c23801
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23801_3
  · exact m23801_9
  · exact m23801_10
  · exact m23801_33
  · exact m23801_34
  · exact m23801_40

def b23802 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 70 148 138 57 41 105 169 297), lower := (rows 321 70 148 138 16 32 64 128 256), losses := [] }

theorem u23802 : Upper (D 8) (R 8) [320,68,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23803_3 : Upper (D 8) (R 8) [320,68,144,160,3] 13 :=
  permutation_upper _ _ _ [320,5,72,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18055

theorem m23803_9 : Upper (D 8) (R 8) [320,68,144,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18227

theorem m23803_10 : Upper (D 8) (R 8) [320,68,144,160,10] 13 :=
  permutation_upper _ _ _ [320,12,80,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18429

theorem m23803_33 : Upper (D 8) (R 8) [320,68,144,160,33] 13 :=
  permutation_upper _ _ _ [320,33,72,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18607

theorem m23803_34 : Upper (D 8) (R 8) [320,68,144,160,34] 13 :=
  permutation_upper _ _ _ [320,36,72,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18685

theorem m23803_40 : Upper (D 8) (R 8) [320,68,144,160,40] 13 :=
  permutation_upper _ _ _ [320,36,160,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18750

def r23803 : Route 9 := (fun mask => (mask,id))

def c23803 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23803 : Upper (D 8) (R 8) [320,68,144,160] 13 := by
  apply FastRouting.sound _ _ [320,68,144,160] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23803 c23803
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23803_3
  · exact m23803_9
  · exact m23803_10
  · exact m23803_33
  · exact m23803_34
  · exact m23803_40

theorem m23804_3 : Upper (D 8) (R 8) [320,68,160,129,3] 13 :=
  permutation_upper _ _ _ [320,5,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18060

theorem m23804_9 : Upper (D 8) (R 8) [320,68,160,129,9] 13 :=
  permutation_upper _ _ _ [320,5,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18100

theorem m23804_10 : Upper (D 8) (R 8) [320,68,160,129,10] 13 :=
  permutation_upper _ _ _ [320,12,80,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18422

theorem m23804_33 : Upper (D 8) (R 8) [320,68,160,129,33] 13 :=
  permutation_upper _ _ _ [320,33,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18615

theorem m23804_34 : Upper (D 8) (R 8) [320,68,160,129,34] 13 :=
  permutation_upper _ _ _ [320,36,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18689

theorem m23804_40 : Upper (D 8) (R 8) [320,68,160,129,40] 13 :=
  permutation_upper _ _ _ [320,36,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18711

def r23804 : Route 9 := (fun mask => (mask,id))

def c23804 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23804 : Upper (D 8) (R 8) [320,68,160,129] 13 := by
  apply FastRouting.sound _ _ [320,68,160,129] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23804 c23804
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23804_3
  · exact m23804_9
  · exact m23804_10
  · exact m23804_33
  · exact m23804_34
  · exact m23804_40

def b23805 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 70 164 138 57 57 121 185 313), lower := (rows 321 70 164 138 16 32 64 128 256), losses := [] }

theorem u23805 : Upper (D 8) (R 8) [320,68,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23806_3 : Upper (D 8) (R 8) [320,68,160,144,3] 13 :=
  permutation_upper _ _ _ [320,5,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18061

theorem m23806_9 : Upper (D 8) (R 8) [320,68,160,144,9] 13 :=
  permutation_upper _ _ _ [320,5,130,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18121

theorem m23806_10 : Upper (D 8) (R 8) [320,68,160,144,10] 13 :=
  permutation_upper _ _ _ [320,12,80,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18425

theorem m23806_33 : Upper (D 8) (R 8) [320,68,160,144,33] 13 :=
  permutation_upper _ _ _ [320,33,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18616

theorem m23806_34 : Upper (D 8) (R 8) [320,68,160,144,34] 13 :=
  permutation_upper _ _ _ [320,36,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18690

theorem m23806_40 : Upper (D 8) (R 8) [320,68,160,144,40] 13 :=
  permutation_upper _ _ _ [320,36,130,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18721

def r23806 : Route 9 := (fun mask => (mask,id))

def c23806 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23806 : Upper (D 8) (R 8) [320,68,160,144] 13 := by
  apply FastRouting.sound _ _ [320,68,160,144] 13 (by decide) (choices 2) [3,9,10,33,34,40] r23806 c23806
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23806_3
  · exact m23806_9
  · exact m23806_10
  · exact m23806_33
  · exact m23806_34
  · exact m23806_40

def b23807 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 70 164 168 59 59 123 187 315), lower := (rows 321 70 164 168 16 32 64 128 256), losses := [] }

theorem u23807 : Upper (D 8) (R 8) [320,68,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23808_5 : Upper (D 8) (R 8) [320,80,129,130,5] 13 :=
  permutation_upper _ _ _ [320,5,129,66,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18097

theorem m23808_9 : Upper (D 8) (R 8) [320,80,129,130,9] 13 :=
  permutation_upper _ _ _ [320,5,136,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18157

theorem m23808_12 : Upper (D 8) (R 8) [320,80,129,130,12] 13 :=
  permutation_upper _ _ _ [320,12,129,144,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18456

theorem m23808_33 : Upper (D 8) (R 8) [320,80,129,130,33] 13 :=
  permutation_upper _ _ _ [320,33,66,129,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18594

theorem m23808_36 : Upper (D 8) (R 8) [320,80,129,130,36] 13 :=
  permutation_upper _ _ _ [320,36,129,66,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18706

theorem m23808_40 : Upper (D 8) (R 8) [320,80,129,130,40] 13 :=
  permutation_upper _ _ _ [320,36,136,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18730

def r23808 : Route 9 := (fun mask => (mask,id))

def c23808 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23808 : Upper (D 8) (R 8) [320,80,129,130] 13 := by
  apply FastRouting.sound _ _ [320,80,129,130] 13 (by decide) (choices 2) [5,9,12,33,36,40] r23808 c23808
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23808_5
  · exact m23808_9
  · exact m23808_12
  · exact m23808_33
  · exact m23808_36
  · exact m23808_40

theorem m23809_3 : Upper (D 8) (R 8) [320,80,129,160,3] 13 :=
  permutation_upper _ _ _ [320,5,66,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18036

theorem m23809_5 : Upper (D 8) (R 8) [320,80,129,160,5] 13 :=
  permutation_upper _ _ _ [320,5,129,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18098

theorem m23809_6 : Upper (D 8) (R 8) [320,80,129,160,6] 13 :=
  permutation_upper _ _ _ [320,12,66,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18414

theorem m23809_9 : Upper (D 8) (R 8) [320,80,129,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18223

theorem m23809_10 : Upper (D 8) (R 8) [320,80,129,160,10] 13 :=
  permutation_upper _ _ _ [320,12,66,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18417

theorem m23809_12 : Upper (D 8) (R 8) [320,80,129,160,12] 13 :=
  permutation_upper _ _ _ [320,12,129,160,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18460

theorem m23809_33 : Upper (D 8) (R 8) [320,80,129,160,33] 13 :=
  permutation_upper _ _ _ [320,33,66,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18596

theorem m23809_34 : Upper (D 8) (R 8) [320,80,129,160,34] 13 :=
  permutation_upper _ _ _ [320,36,66,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18677

theorem m23809_36 : Upper (D 8) (R 8) [320,80,129,160,36] 13 :=
  permutation_upper _ _ _ [320,36,129,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18707

theorem m23809_40 : Upper (D 8) (R 8) [320,80,129,160,40] 13 :=
  permutation_upper _ _ _ [320,36,160,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18746

def r23809 : Route 9 := (fun mask => (mask,id))

def c23809 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23809 : Upper (D 8) (R 8) [320,80,129,160] 13 := by
  apply FastRouting.sound _ _ [320,80,129,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r23809 c23809
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23809_3
  · exact m23809_5
  · exact m23809_6
  · exact m23809_9
  · exact m23809_10
  · exact m23809_12
  · exact m23809_33
  · exact m23809_34
  · exact m23809_36
  · exact m23809_40

theorem m23810_5 : Upper (D 8) (R 8) [320,80,130,160,5] 13 :=
  permutation_upper _ _ _ [320,5,136,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18158

theorem m23810_9 : Upper (D 8) (R 8) [320,80,130,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,66,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18224

theorem m23810_12 : Upper (D 8) (R 8) [320,80,130,160,12] 13 :=
  permutation_upper _ _ _ [320,12,144,160,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18471

theorem m23810_33 : Upper (D 8) (R 8) [320,80,130,160,33] 13 :=
  permutation_upper _ _ _ [320,33,66,132,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18598

theorem m23810_36 : Upper (D 8) (R 8) [320,80,130,160,36] 13 :=
  permutation_upper _ _ _ [320,36,136,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18731

theorem m23810_40 : Upper (D 8) (R 8) [320,80,130,160,40] 13 :=
  permutation_upper _ _ _ [320,36,160,66,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18747

def r23810 : Route 9 := (fun mask => (mask,id))

def c23810 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23810 : Upper (D 8) (R 8) [320,80,130,160] 13 := by
  apply FastRouting.sound _ _ [320,80,130,160] 13 (by decide) (choices 2) [5,9,12,33,36,40] r23810 c23810
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23810_5
  · exact m23810_9
  · exact m23810_12
  · exact m23810_33
  · exact m23810_36
  · exact m23810_40

def b23811 : PairBound 9 := { available := 62, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 321 98 133 137 62 62 126 190 318), lower := (rows 321 98 133 137 16 32 64 128 256), losses := [] }

theorem u23811 : Upper (D 8) (R 8) [320,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23812_5 : Upper (D 8) (R 8) [320,96,129,130,5] 13 :=
  permutation_upper _ _ _ [320,5,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18102

theorem m23812_9 : Upper (D 8) (R 8) [320,96,129,130,9] 13 :=
  permutation_upper _ _ _ [320,5,136,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18166

theorem m23812_12 : Upper (D 8) (R 8) [320,96,129,130,12] 13 :=
  permutation_upper _ _ _ [320,12,129,144,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18457

theorem m23812_33 : Upper (D 8) (R 8) [320,96,129,130,33] 13 :=
  permutation_upper _ _ _ [320,33,96,129,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18620

theorem m23812_36 : Upper (D 8) (R 8) [320,96,129,130,36] 13 :=
  permutation_upper _ _ _ [320,36,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18714

theorem m23812_40 : Upper (D 8) (R 8) [320,96,129,130,40] 13 :=
  permutation_upper _ _ _ [320,36,136,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18735

def r23812 : Route 9 := (fun mask => (mask,id))

def c23812 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23812 : Upper (D 8) (R 8) [320,96,129,130] 13 := by
  apply FastRouting.sound _ _ [320,96,129,130] 13 (by decide) (choices 2) [5,9,12,33,36,40] r23812 c23812
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23812_5
  · exact m23812_9
  · exact m23812_12
  · exact m23812_33
  · exact m23812_36
  · exact m23812_40

def b23813 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 98 133 140 59 59 123 187 315), lower := (rows 321 98 133 140 16 32 64 128 256), losses := [] }

theorem u23813 : Upper (D 8) (R 8) [320,96,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23813 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23814_3 : Upper (D 8) (R 8) [320,96,129,144,3] 13 :=
  permutation_upper _ _ _ [320,5,96,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18080

theorem m23814_5 : Upper (D 8) (R 8) [320,96,129,144,5] 13 :=
  permutation_upper _ _ _ [320,5,129,96,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18101

theorem m23814_6 : Upper (D 8) (R 8) [320,96,129,144,6] 13 :=
  permutation_upper _ _ _ [320,12,96,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18434

theorem m23814_9 : Upper (D 8) (R 8) [320,96,129,144,9] 13 :=
  permutation_upper _ _ _ [320,5,130,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18122

theorem m23814_10 : Upper (D 8) (R 8) [320,96,129,144,10] 13 :=
  permutation_upper _ _ _ [320,12,96,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18437

theorem m23814_12 : Upper (D 8) (R 8) [320,96,129,144,12] 13 :=
  permutation_upper _ _ _ [320,12,129,130,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18453

theorem m23814_33 : Upper (D 8) (R 8) [320,96,129,144,33] 13 :=
  permutation_upper _ _ _ [320,33,96,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18619

theorem m23814_34 : Upper (D 8) (R 8) [320,96,129,144,34] 13 :=
  permutation_upper _ _ _ [320,36,96,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18695

theorem m23814_36 : Upper (D 8) (R 8) [320,96,129,144,36] 13 :=
  permutation_upper _ _ _ [320,36,129,96,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18713

theorem m23814_40 : Upper (D 8) (R 8) [320,96,129,144,40] 13 :=
  permutation_upper _ _ _ [320,36,130,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18722

def r23814 : Route 9 := (fun mask => (mask,id))

def c23814 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23814 : Upper (D 8) (R 8) [320,96,129,144] 13 := by
  apply FastRouting.sound _ _ [320,96,129,144] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r23814 c23814
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23814_3
  · exact m23814_5
  · exact m23814_6
  · exact m23814_9
  · exact m23814_10
  · exact m23814_12
  · exact m23814_33
  · exact m23814_34
  · exact m23814_36
  · exact m23814_40

theorem m23815_3 : Upper (D 8) (R 8) [320,96,129,160,3] 13 :=
  permutation_upper _ _ _ [320,5,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18081

theorem m23815_5 : Upper (D 8) (R 8) [320,96,129,160,5] 13 :=
  permutation_upper _ _ _ [320,5,129,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18103

theorem m23815_6 : Upper (D 8) (R 8) [320,96,129,160,6] 13 :=
  permutation_upper _ _ _ [320,12,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18435

theorem m23815_9 : Upper (D 8) (R 8) [320,96,129,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18230

theorem m23815_10 : Upper (D 8) (R 8) [320,96,129,160,10] 13 :=
  permutation_upper _ _ _ [320,12,96,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18446

theorem m23815_12 : Upper (D 8) (R 8) [320,96,129,160,12] 13 :=
  permutation_upper _ _ _ [320,12,129,160,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18461

theorem m23815_33 : Upper (D 8) (R 8) [320,96,129,160,33] 13 :=
  permutation_upper _ _ _ [320,33,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18622

theorem m23815_34 : Upper (D 8) (R 8) [320,96,129,160,34] 13 :=
  permutation_upper _ _ _ [320,36,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18696

theorem m23815_36 : Upper (D 8) (R 8) [320,96,129,160,36] 13 :=
  permutation_upper _ _ _ [320,36,129,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18715

theorem m23815_40 : Upper (D 8) (R 8) [320,96,129,160,40] 13 :=
  permutation_upper _ _ _ [320,36,160,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18752

def r23815 : Route 9 := (fun mask => (mask,id))

def c23815 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23815 : Upper (D 8) (R 8) [320,96,129,160] 13 := by
  apply FastRouting.sound _ _ [320,96,129,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r23815 c23815
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23815_3
  · exact m23815_5
  · exact m23815_6
  · exact m23815_9
  · exact m23815_10
  · exact m23815_12
  · exact m23815_33
  · exact m23815_34
  · exact m23815_36
  · exact m23815_40

def b23816 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 98 134 140 57 57 121 185 313), lower := (rows 321 98 134 140 16 32 64 128 256), losses := [] }

theorem u23816 : Upper (D 8) (R 8) [320,96,130,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23817_5 : Upper (D 8) (R 8) [320,96,130,144,5] 13 :=
  permutation_upper _ _ _ [320,5,136,96,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18167

theorem m23817_9 : Upper (D 8) (R 8) [320,96,130,144,9] 13 :=
  permutation_upper _ _ _ [320,5,130,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18123

theorem m23817_12 : Upper (D 8) (R 8) [320,96,130,144,12] 13 :=
  permutation_upper _ _ _ [320,12,130,144,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18465

theorem m23817_33 : Upper (D 8) (R 8) [320,96,130,144,33] 13 :=
  permutation_upper _ _ _ [320,33,96,130,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18623

theorem m23817_36 : Upper (D 8) (R 8) [320,96,130,144,36] 13 :=
  permutation_upper _ _ _ [320,36,136,96,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18736

theorem m23817_40 : Upper (D 8) (R 8) [320,96,130,144,40] 13 :=
  permutation_upper _ _ _ [320,36,130,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18723

def r23817 : Route 9 := (fun mask => (mask,id))

def c23817 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23817 : Upper (D 8) (R 8) [320,96,130,144] 13 := by
  apply FastRouting.sound _ _ [320,96,130,144] 13 (by decide) (choices 2) [5,9,12,33,36,40] r23817 c23817
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23817_5
  · exact m23817_9
  · exact m23817_12
  · exact m23817_33
  · exact m23817_36
  · exact m23817_40

theorem m23818_5 : Upper (D 8) (R 8) [320,96,130,160,5] 13 :=
  permutation_upper _ _ _ [320,5,136,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18168

theorem m23818_9 : Upper (D 8) (R 8) [320,96,130,160,9] 13 :=
  permutation_upper _ _ _ [320,5,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18232

theorem m23818_12 : Upper (D 8) (R 8) [320,96,130,160,12] 13 :=
  permutation_upper _ _ _ [320,12,144,160,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18472

theorem m23818_33 : Upper (D 8) (R 8) [320,96,130,160,33] 13 :=
  permutation_upper _ _ _ [320,33,96,132,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18627

theorem m23818_36 : Upper (D 8) (R 8) [320,96,130,160,36] 13 :=
  permutation_upper _ _ _ [320,36,136,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18737

theorem m23818_40 : Upper (D 8) (R 8) [320,96,130,160,40] 13 :=
  permutation_upper _ _ _ [320,36,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u18754

def r23818 : Route 9 := (fun mask => (mask,id))

def c23818 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u23818 : Upper (D 8) (R 8) [320,96,130,160] 13 := by
  apply FastRouting.sound _ _ [320,96,130,160] 13 (by decide) (choices 2) [5,9,12,33,36,40] r23818 c23818
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23818_5
  · exact m23818_9
  · exact m23818_12
  · exact m23818_33
  · exact m23818_36
  · exact m23818_40

def b23819 : PairBound 9 := { available := 51, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 98 140 140 51 51 115 179 307), lower := (rows 321 98 140 140 16 32 64 128 256), losses := [] }

theorem u23819 : Upper (D 8) (R 8) [320,96,136,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u23819
end Delivery.IrregularNine14.P08
