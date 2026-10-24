import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0285
import IrregularNine14P08C0286
import IrregularNine14P08C0287
import IrregularNine14P08C0289
import IrregularNine14P08C0290
import IrregularNine14P08C0291
import IrregularNine14P08C0292
import IrregularNine14P08C0293
import IrregularNine14P08C0294
import IrregularNine14P08C0295

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23160 : PairBound 9 := { available := 215, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 76 168 215 247 215 215 471), lower := (rows 289 35 76 168 16 32 64 128 256), losses := [] }

theorem u23160 : Upper (D 8) (R 8) [288,33,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23161 : PairBound 9 := { available := 159, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 289 35 100 200 159 191 223 159 415), lower := (rows 289 35 100 200 16 32 64 128 256), losses := [] }

theorem u23161 : Upper (D 8) (R 8) [288,33,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23162 : PairBound 9 := { available := 217, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 38 73 217 249 217 217 473), lower := (rows 289 38 38 73 16 32 64 128 256), losses := [] }

theorem u23162 : Upper (D 8) (R 8) [288,36,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23163 : PairBound 9 := { available := 217, camps := [{ cop := 5, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 38 200 217 249 217 217 473), lower := (rows 289 38 38 200 16 32 64 128 256), losses := [] }

theorem u23163 : Upper (D 8) (R 8) [288,36,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23164 : PairBound 9 := { available := 211, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 73 211 243 211 211 467), lower := (rows 289 38 44 73 16 32 64 128 256), losses := [] }

theorem u23164 : Upper (D 8) (R 8) [288,36,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23165 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 74 209 241 209 209 465), lower := (rows 289 38 44 74 16 32 64 128 256), losses := [] }

theorem u23165 : Upper (D 8) (R 8) [288,36,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23166 : PairBound 9 := { available := 211, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 44 200 211 243 211 211 467), lower := (rows 289 38 44 200 16 32 64 128 256), losses := [] }

theorem u23166 : Upper (D 8) (R 8) [288,36,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23167 : PairBound 9 := { available := 203, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 52 73 219 235 203 203 459), lower := (rows 289 38 52 73 16 32 64 128 256), losses := [] }

theorem u23167 : Upper (D 8) (R 8) [288,36,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23168 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 52 74 217 233 201 201 457), lower := (rows 289 38 52 74 16 32 64 128 256), losses := [] }

theorem u23168 : Upper (D 8) (R 8) [288,36,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23169 : PairBound 9 := { available := 203, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 52 200 219 235 203 203 459), lower := (rows 289 38 52 200 16 32 64 128 256), losses := [] }

theorem u23169 : Upper (D 8) (R 8) [288,36,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23170_3 : Upper (D 8) (R 8) [288,36,65,48,3] 13 :=
  permutation_upper _ _ _ [288,5,40,65,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17157

theorem m23170_9 : Upper (D 8) (R 8) [288,36,65,48,9] 13 :=
  permutation_upper _ _ _ [288,5,34,48,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17132

theorem m23170_10 : Upper (D 8) (R 8) [288,36,65,48,10] 13 :=
  permutation_upper _ _ _ [288,12,34,48,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17441

def r23170 : Route 9 := (fun mask => (mask,id))

def c23170 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23170 : Upper (D 8) (R 8) [288,36,65,48] 13 := by
  apply FastRouting.sound _ _ [288,36,65,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r23170 c23170
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23170_3
  · exact m23170_9
  · exact m23170_10
  · exact u17636
  · exact u17637
  · exact u17638
  · exact u17639
  · exact u17640
  · exact u17641
  · exact u17642

def b23171 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 289 38 69 73 186 186 250 186 442), lower := (rows 289 38 69 73 16 32 64 128 256), losses := [] }

theorem u23171 : Upper (D 8) (R 8) [288,36,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23172 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 74 185 185 249 185 441), lower := (rows 289 38 69 74 16 32 64 128 256), losses := [] }

theorem u23172 : Upper (D 8) (R 8) [288,36,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23173_3 : Upper (D 8) (R 8) [288,36,65,80,3] 13 :=
  permutation_upper _ _ _ [288,5,40,65,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17158

theorem m23173_9 : Upper (D 8) (R 8) [288,36,65,80,9] 13 :=
  permutation_upper _ _ _ [288,5,66,48,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17224

theorem m23173_10 : Upper (D 8) (R 8) [288,36,65,80,10] 13 :=
  permutation_upper _ _ _ [288,12,48,66,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17472

theorem m23173_33 : Upper (D 8) (R 8) [288,36,65,80,33] 13 :=
  permutation_upper _ _ _ [288,33,40,65,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17585

theorem m23173_34 : Upper (D 8) (R 8) [288,36,65,80,34] 13 :=
  permutation_upper _ _ _ [288,36,40,65,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17625

theorem m23173_40 : Upper (D 8) (R 8) [288,36,65,80,40] 13 :=
  permutation_upper _ _ _ [288,36,65,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17638

def r23173 : Route 9 := (fun mask => (mask,id))

def c23173 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23173 : Upper (D 8) (R 8) [288,36,65,80] 13 := by
  apply FastRouting.sound _ _ [288,36,65,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23173 c23173
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23173_3
  · exact m23173_9
  · exact m23173_10
  · exact m23173_33
  · exact m23173_34
  · exact m23173_40
  · exact u17649
  · exact u17650
  · exact u17651
  · exact u17652

theorem m23174_3 : Upper (D 8) (R 8) [288,36,65,96,3] 13 :=
  permutation_upper _ _ _ [288,5,40,65,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17159

theorem m23174_9 : Upper (D 8) (R 8) [288,36,65,96,9] 13 :=
  permutation_upper _ _ _ [288,5,96,48,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17345

theorem m23174_10 : Upper (D 8) (R 8) [288,36,65,96,10] 13 :=
  permutation_upper _ _ _ [288,12,48,96,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17477

def r23174 : Route 9 := (fun mask => (mask,id))

def c23174 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23174 : Upper (D 8) (R 8) [288,36,65,96] 13 := by
  apply FastRouting.sound _ _ [288,36,65,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r23174 c23174
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23174_3
  · exact m23174_9
  · exact m23174_10
  · exact u17653
  · exact u17654
  · exact u17655

theorem m23175_10 : Upper (D 8) (R 8) [288,36,65,129,10] 13 :=
  permutation_upper _ _ _ [288,12,48,65,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17467

theorem m23175_34 : Upper (D 8) (R 8) [288,36,65,129,34] 13 :=
  permutation_upper _ _ _ [288,36,40,65,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17626

theorem m23175_40 : Upper (D 8) (R 8) [288,36,65,129,40] 13 :=
  permutation_upper _ _ _ [288,36,65,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17639

theorem m23175_66 : Upper (D 8) (R 8) [288,36,65,129,66] 13 :=
  permutation_upper _ _ _ [288,36,65,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17646

theorem m23175_72 : Upper (D 8) (R 8) [288,36,65,129,72] 13 :=
  permutation_upper _ _ _ [288,36,65,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17649

theorem m23175_96 : Upper (D 8) (R 8) [288,36,65,129,96] 13 :=
  permutation_upper _ _ _ [288,36,65,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17653

def r23175 : Route 9 := (fun mask => (mask,id))

def c23175 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23175 : Upper (D 8) (R 8) [288,36,65,129] 13 := by
  apply FastRouting.sound _ _ [288,36,65,129] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r23175 c23175
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23175_10
  · exact m23175_34
  · exact m23175_40
  · exact m23175_66
  · exact m23175_72
  · exact m23175_96
  · exact u17656
  · exact u17657
  · exact u17658
  · exact u17659

theorem m23176_9 : Upper (D 8) (R 8) [288,36,65,130,9] 13 :=
  permutation_upper _ _ _ [288,5,72,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17273

theorem m23176_33 : Upper (D 8) (R 8) [288,36,65,130,33] 13 :=
  permutation_upper _ _ _ [288,33,40,65,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17587

theorem m23176_40 : Upper (D 8) (R 8) [288,36,65,130,40] 13 :=
  permutation_upper _ _ _ [288,36,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17640

theorem m23176_65 : Upper (D 8) (R 8) [288,36,65,130,65] 13 :=
  permutation_upper _ _ _ [288,36,65,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17643

theorem m23176_72 : Upper (D 8) (R 8) [288,36,65,130,72] 13 :=
  permutation_upper _ _ _ [288,36,65,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17650

theorem m23176_96 : Upper (D 8) (R 8) [288,36,65,130,96] 13 :=
  permutation_upper _ _ _ [288,36,65,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17654

theorem m23176_129 : Upper (D 8) (R 8) [288,36,65,130,129] 13 :=
  permutation_upper _ _ _ [288,36,65,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17656

def r23176 : Route 9 := (fun mask => (mask,id))

def c23176 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23176 : Upper (D 8) (R 8) [288,36,65,130] 13 := by
  apply FastRouting.sound _ _ [288,36,65,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23176 c23176
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23176_9
  · exact m23176_33
  · exact m23176_40
  · exact m23176_65
  · exact m23176_72
  · exact m23176_96
  · exact m23176_129
  · exact u17660
  · exact u17661
  · exact u17662

theorem m23177_3 : Upper (D 8) (R 8) [288,36,65,144,3] 13 :=
  permutation_upper _ _ _ [288,5,40,65,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17160

theorem m23177_9 : Upper (D 8) (R 8) [288,36,65,144,9] 13 :=
  permutation_upper _ _ _ [288,5,66,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17227

theorem m23177_10 : Upper (D 8) (R 8) [288,36,65,144,10] 13 :=
  permutation_upper _ _ _ [288,12,48,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17474

theorem m23177_33 : Upper (D 8) (R 8) [288,36,65,144,33] 13 :=
  permutation_upper _ _ _ [288,33,40,65,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17586

theorem m23177_34 : Upper (D 8) (R 8) [288,36,65,144,34] 13 :=
  permutation_upper _ _ _ [288,36,40,65,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17627

theorem m23177_40 : Upper (D 8) (R 8) [288,36,65,144,40] 13 :=
  permutation_upper _ _ _ [288,36,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17641

theorem m23177_65 : Upper (D 8) (R 8) [288,36,65,144,65] 13 :=
  permutation_upper _ _ _ [288,36,65,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17644

theorem m23177_66 : Upper (D 8) (R 8) [288,36,65,144,66] 13 :=
  permutation_upper _ _ _ [288,36,65,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17647

theorem m23177_72 : Upper (D 8) (R 8) [288,36,65,144,72] 13 :=
  permutation_upper _ _ _ [288,36,65,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17651

theorem m23177_96 : Upper (D 8) (R 8) [288,36,65,144,96] 13 :=
  permutation_upper _ _ _ [288,36,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17655

theorem m23177_129 : Upper (D 8) (R 8) [288,36,65,144,129] 13 :=
  permutation_upper _ _ _ [288,36,65,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17657

theorem m23177_130 : Upper (D 8) (R 8) [288,36,65,144,130] 13 :=
  permutation_upper _ _ _ [288,36,65,130,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17660

def r23177 : Route 9 := (fun mask => (mask,id))

def c23177 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23177 : Upper (D 8) (R 8) [288,36,65,144] 13 := by
  apply FastRouting.sound _ _ [288,36,65,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r23177 c23177
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23177_3
  · exact m23177_9
  · exact m23177_10
  · exact m23177_33
  · exact m23177_34
  · exact m23177_40
  · exact m23177_65
  · exact m23177_66
  · exact m23177_72
  · exact m23177_96
  · exact m23177_129
  · exact m23177_130
  · exact u17663
  · exact u17664
  · exact u17665

theorem m23178_3 : Upper (D 8) (R 8) [288,36,65,160,3] 13 :=
  permutation_upper _ _ _ [288,5,40,65,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17161

theorem m23178_9 : Upper (D 8) (R 8) [288,36,65,160,9] 13 :=
  permutation_upper _ _ _ [288,5,96,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17348

theorem m23178_10 : Upper (D 8) (R 8) [288,36,65,160,10] 13 :=
  permutation_upper _ _ _ [288,12,48,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17479

theorem m23178_65 : Upper (D 8) (R 8) [288,36,65,160,65] 13 :=
  permutation_upper _ _ _ [288,36,65,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17645

theorem m23178_66 : Upper (D 8) (R 8) [288,36,65,160,66] 13 :=
  permutation_upper _ _ _ [288,36,65,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17648

theorem m23178_72 : Upper (D 8) (R 8) [288,36,65,160,72] 13 :=
  permutation_upper _ _ _ [288,36,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17652

theorem m23178_129 : Upper (D 8) (R 8) [288,36,65,160,129] 13 :=
  permutation_upper _ _ _ [288,36,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17658

theorem m23178_130 : Upper (D 8) (R 8) [288,36,65,160,130] 13 :=
  permutation_upper _ _ _ [288,36,65,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17661

theorem m23178_136 : Upper (D 8) (R 8) [288,36,65,160,136] 13 :=
  permutation_upper _ _ _ [288,36,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17664

def r23178 : Route 9 := (fun mask => (mask,id))

def c23178 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23178 : Upper (D 8) (R 8) [288,36,65,160] 13 := by
  apply FastRouting.sound _ _ [288,36,65,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r23178 c23178
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23178_3
  · exact m23178_9
  · exact m23178_10
  · exact m23178_65
  · exact m23178_66
  · exact m23178_72
  · exact m23178_129
  · exact m23178_130
  · exact m23178_136
  · exact u17666

theorem m23179_3 : Upper (D 8) (R 8) [288,36,65,192,3] 13 :=
  permutation_upper _ _ _ [288,5,40,65,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17162

theorem m23179_9 : Upper (D 8) (R 8) [288,36,65,192,9] 13 :=
  permutation_upper _ _ _ [288,5,192,48,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17393

theorem m23179_10 : Upper (D 8) (R 8) [288,36,65,192,10] 13 :=
  permutation_upper _ _ _ [288,12,48,192,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17484

theorem m23179_33 : Upper (D 8) (R 8) [288,36,65,192,33] 13 :=
  permutation_upper _ _ _ [288,33,40,65,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17588

theorem m23179_34 : Upper (D 8) (R 8) [288,36,65,192,34] 13 :=
  permutation_upper _ _ _ [288,36,40,65,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17628

theorem m23179_40 : Upper (D 8) (R 8) [288,36,65,192,40] 13 :=
  permutation_upper _ _ _ [288,36,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17642

theorem m23179_129 : Upper (D 8) (R 8) [288,36,65,192,129] 13 :=
  permutation_upper _ _ _ [288,36,65,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17659

theorem m23179_130 : Upper (D 8) (R 8) [288,36,65,192,130] 13 :=
  permutation_upper _ _ _ [288,36,65,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17662

theorem m23179_136 : Upper (D 8) (R 8) [288,36,65,192,136] 13 :=
  permutation_upper _ _ _ [288,36,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17665

theorem m23179_160 : Upper (D 8) (R 8) [288,36,65,192,160] 13 :=
  permutation_upper _ _ _ [288,36,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17666

def r23179 : Route 9 := (fun mask => (mask,id))

def c23179 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23179 : Upper (D 8) (R 8) [288,36,65,192] 13 := by
  apply FastRouting.sound _ _ [288,36,65,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23179 c23179
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23179_3
  · exact m23179_9
  · exact m23179_10
  · exact m23179_33
  · exact m23179_34
  · exact m23179_40
  · exact m23179_129
  · exact m23179_130
  · exact m23179_136
  · exact m23179_160

theorem m23180_9 : Upper (D 8) (R 8) [288,36,66,48,9] 13 :=
  permutation_upper _ _ _ [288,5,34,48,72] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17133

theorem m23180_65 : Upper (D 8) (R 8) [288,36,66,48,65] 13 :=
  permutation_upper _ _ _ [288,36,65,48,72] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17638

theorem m23180_129 : Upper (D 8) (R 8) [288,36,66,48,129] 13 :=
  permutation_upper _ _ _ [288,36,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17641

def r23180 : Route 9 := (fun mask => (mask,id))

def c23180 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23180 : Upper (D 8) (R 8) [288,36,66,48] 13 := by
  apply FastRouting.sound _ _ [288,36,66,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r23180 c23180
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23180_9
  · exact m23180_65
  · exact u17667
  · exact m23180_129
  · exact u17668
  · exact u17669

def b23181 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 73 185 185 249 185 441), lower := (rows 289 38 70 73 16 32 64 128 256), losses := [] }

theorem u23181 : Upper (D 8) (R 8) [288,36,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23181 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23182 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 88 185 169 233 169 425), lower := (rows 289 38 70 88 16 32 64 128 256), losses := [] }

theorem u23182 : Upper (D 8) (R 8) [288,36,66,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23182 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23183 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 70 104 153 185 217 153 409), lower := (rows 289 38 70 104 16 32 64 128 256), losses := [] }

theorem u23183 : Upper (D 8) (R 8) [288,36,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23183 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23184_9 : Upper (D 8) (R 8) [288,36,66,129,9] 13 :=
  permutation_upper _ _ _ [288,5,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17203

theorem m23184_33 : Upper (D 8) (R 8) [288,36,66,129,33] 13 :=
  permutation_upper _ _ _ [288,33,40,68,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17593

theorem m23184_40 : Upper (D 8) (R 8) [288,36,66,129,40] 13 :=
  permutation_upper _ _ _ [288,36,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17641

theorem m23184_65 : Upper (D 8) (R 8) [288,36,66,129,65] 13 :=
  permutation_upper _ _ _ [288,36,66,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17670

theorem m23184_72 : Upper (D 8) (R 8) [288,36,66,129,72] 13 :=
  permutation_upper _ _ _ [288,36,66,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17673

theorem m23184_96 : Upper (D 8) (R 8) [288,36,66,129,96] 13 :=
  permutation_upper _ _ _ [288,36,66,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17676

def r23184 : Route 9 := (fun mask => (mask,id))

def c23184 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23184 : Upper (D 8) (R 8) [288,36,66,129] 13 := by
  apply FastRouting.sound _ _ [288,36,66,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23184 c23184
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23184_9
  · exact m23184_33
  · exact m23184_40
  · exact m23184_65
  · exact m23184_72
  · exact m23184_96
  · exact u17678
  · exact u17679
  · exact u17680
  · exact u17681

theorem m23185_9 : Upper (D 8) (R 8) [288,36,66,144,9] 13 :=
  permutation_upper _ _ _ [288,5,66,48,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17228

theorem m23185_33 : Upper (D 8) (R 8) [288,36,66,144,33] 13 :=
  permutation_upper _ _ _ [288,33,40,68,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17594

theorem m23185_40 : Upper (D 8) (R 8) [288,36,66,144,40] 13 :=
  permutation_upper _ _ _ [288,36,66,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17668

theorem m23185_65 : Upper (D 8) (R 8) [288,36,66,144,65] 13 :=
  permutation_upper _ _ _ [288,36,66,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17671

theorem m23185_72 : Upper (D 8) (R 8) [288,36,66,144,72] 13 :=
  permutation_upper _ _ _ [288,36,66,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17674

theorem m23185_96 : Upper (D 8) (R 8) [288,36,66,144,96] 13 :=
  permutation_upper _ _ _ [288,36,66,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17677

theorem m23185_129 : Upper (D 8) (R 8) [288,36,66,144,129] 13 :=
  permutation_upper _ _ _ [288,36,66,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17679

def r23185 : Route 9 := (fun mask => (mask,id))

def c23185 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23185 : Upper (D 8) (R 8) [288,36,66,144] 13 := by
  apply FastRouting.sound _ _ [288,36,66,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23185 c23185
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23185_9
  · exact m23185_33
  · exact m23185_40
  · exact m23185_65
  · exact m23185_72
  · exact m23185_96
  · exact m23185_129
  · exact u17682
  · exact u17683
  · exact u17684

theorem m23186_9 : Upper (D 8) (R 8) [288,36,66,160,9] 13 :=
  permutation_upper _ _ _ [288,5,96,48,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17350

theorem m23186_65 : Upper (D 8) (R 8) [288,36,66,160,65] 13 :=
  permutation_upper _ _ _ [288,36,66,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17672

theorem m23186_72 : Upper (D 8) (R 8) [288,36,66,160,72] 13 :=
  permutation_upper _ _ _ [288,36,66,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17675

theorem m23186_129 : Upper (D 8) (R 8) [288,36,66,160,129] 13 :=
  permutation_upper _ _ _ [288,36,66,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17680

theorem m23186_136 : Upper (D 8) (R 8) [288,36,66,160,136] 13 :=
  permutation_upper _ _ _ [288,36,66,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17683

def r23186 : Route 9 := (fun mask => (mask,id))

def c23186 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23186 : Upper (D 8) (R 8) [288,36,66,160] 13 := by
  apply FastRouting.sound _ _ [288,36,66,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r23186 c23186
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23186_9
  · exact m23186_65
  · exact m23186_72
  · exact m23186_129
  · exact m23186_136
  · exact u17685

def b23187 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 70 200 185 185 249 185 441), lower := (rows 289 38 70 200 16 32 64 128 256), losses := [] }

theorem u23187 : Upper (D 8) (R 8) [288,36,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23187 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23188_3 : Upper (D 8) (R 8) [288,36,72,48,3] 13 :=
  permutation_upper _ _ _ [288,5,40,80,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17170

theorem m23188_65 : Upper (D 8) (R 8) [288,36,72,48,65] 13 :=
  permutation_upper _ _ _ [288,36,65,48,66] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17637

theorem m23188_129 : Upper (D 8) (R 8) [288,36,72,48,129] 13 :=
  permutation_upper _ _ _ [288,36,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17640

def r23188 : Route 9 := (fun mask => (mask,id))

def c23188 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23188 : Upper (D 8) (R 8) [288,36,72,48] 13 := by
  apply FastRouting.sound _ _ [288,36,72,48] 13 (by decide) (choices 2) [3,65,66,129,130,192] r23188 c23188
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23188_3
  · exact m23188_65
  · exact u17686
  · exact m23188_129
  · exact u17687
  · exact u17688

def b23189 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 73 179 179 243 179 435), lower := (rows 289 38 76 73 16 32 64 128 256), losses := [] }

theorem u23189 : Upper (D 8) (R 8) [288,36,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23189 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23190 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 74 177 177 241 177 433), lower := (rows 289 38 76 74 16 32 64 128 256), losses := [] }

theorem u23190 : Upper (D 8) (R 8) [288,36,72,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23190 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23191 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 88 179 163 227 163 419), lower := (rows 289 38 76 88 16 32 64 128 256), losses := [] }

theorem u23191 : Upper (D 8) (R 8) [288,36,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23191 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23192 : PairBound 9 := { available := 147, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 76 104 147 179 211 147 403), lower := (rows 289 38 76 104 16 32 64 128 256), losses := [] }

theorem u23192 : Upper (D 8) (R 8) [288,36,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23192 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23193_3 : Upper (D 8) (R 8) [288,36,72,129,3] 13 :=
  permutation_upper _ _ _ [288,5,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17174

theorem m23193_33 : Upper (D 8) (R 8) [288,36,72,129,33] 13 :=
  permutation_upper _ _ _ [288,33,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17595

theorem m23193_34 : Upper (D 8) (R 8) [288,36,72,129,34] 13 :=
  permutation_upper _ _ _ [288,36,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17632

def r23193 : Route 9 := (fun mask => (mask,id))

def c23193 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23193 : Upper (D 8) (R 8) [288,36,72,129] 13 := by
  apply FastRouting.sound _ _ [288,36,72,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r23193 c23193
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23193_3
  · exact m23193_33
  · exact m23193_34
  · exact u17699
  · exact u17700
  · exact u17701
  · exact u17702
  · exact u17703
  · exact u17704
  · exact u17705

theorem m23194_33 : Upper (D 8) (R 8) [288,36,72,130,33] 13 :=
  permutation_upper _ _ _ [288,33,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17597

def r23194 : Route 9 := (fun mask => (mask,id))

def c23194 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23194 : Upper (D 8) (R 8) [288,36,72,130] 13 := by
  apply FastRouting.sound _ _ [288,36,72,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r23194 c23194
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23194_33
  · exact u17706
  · exact u17707
  · exact u17708
  · exact u17709
  · exact u17710

theorem m23195_3 : Upper (D 8) (R 8) [288,36,72,144,3] 13 :=
  permutation_upper _ _ _ [288,5,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17175

theorem m23195_33 : Upper (D 8) (R 8) [288,36,72,144,33] 13 :=
  permutation_upper _ _ _ [288,33,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17596

theorem m23195_34 : Upper (D 8) (R 8) [288,36,72,144,34] 13 :=
  permutation_upper _ _ _ [288,36,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17633

def r23195 : Route 9 := (fun mask => (mask,id))

def c23195 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23195 : Upper (D 8) (R 8) [288,36,72,144] 13 := by
  apply FastRouting.sound _ _ [288,36,72,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r23195 c23195
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23195_3
  · exact m23195_33
  · exact m23195_34
  · exact u17711
  · exact u17712
  · exact u17713
  · exact u17714
  · exact u17715
  · exact u17716
  · exact u17717

theorem m23196_3 : Upper (D 8) (R 8) [288,36,72,160,3] 13 :=
  permutation_upper _ _ _ [288,5,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17176

def r23196 : Route 9 := (fun mask => (mask,id))

def c23196 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23196 : Upper (D 8) (R 8) [288,36,72,160] 13 := by
  apply FastRouting.sound _ _ [288,36,72,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r23196 c23196
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23196_3
  · exact u17718
  · exact u17719
  · exact u17720
  · exact u17721
  · exact u17722

def b23197 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 200 179 179 243 179 435), lower := (rows 289 38 76 200 16 32 64 128 256), losses := [] }

theorem u23197 : Upper (D 8) (R 8) [288,36,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23197 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23198_3 : Upper (D 8) (R 8) [288,36,80,65,3] 13 :=
  permutation_upper _ _ _ [288,5,40,66,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17164

theorem m23198_9 : Upper (D 8) (R 8) [288,36,80,65,9] 13 :=
  permutation_upper _ _ _ [288,5,65,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17200

theorem m23198_10 : Upper (D 8) (R 8) [288,36,80,65,10] 13 :=
  permutation_upper _ _ _ [288,12,48,65,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17465

theorem m23198_33 : Upper (D 8) (R 8) [288,36,80,65,33] 13 :=
  permutation_upper _ _ _ [288,33,40,66,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17589

theorem m23198_34 : Upper (D 8) (R 8) [288,36,80,65,34] 13 :=
  permutation_upper _ _ _ [288,36,40,66,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17629

theorem m23198_40 : Upper (D 8) (R 8) [288,36,80,65,40] 13 :=
  permutation_upper _ _ _ [288,36,65,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17637

theorem m23198_129 : Upper (D 8) (R 8) [288,36,80,65,129] 13 :=
  permutation_upper _ _ _ [288,36,72,129,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17699

theorem m23198_130 : Upper (D 8) (R 8) [288,36,80,65,130] 13 :=
  permutation_upper _ _ _ [288,36,72,130,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17706

theorem m23198_136 : Upper (D 8) (R 8) [288,36,80,65,136] 13 :=
  permutation_upper _ _ _ [288,36,72,144,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17711

theorem m23198_160 : Upper (D 8) (R 8) [288,36,80,65,160] 13 :=
  permutation_upper _ _ _ [288,36,72,160,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17718

def r23198 : Route 9 := (fun mask => (mask,id))

def c23198 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23198 : Upper (D 8) (R 8) [288,36,80,65] 13 := by
  apply FastRouting.sound _ _ [288,36,80,65] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23198 c23198
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23198_3
  · exact m23198_9
  · exact m23198_10
  · exact m23198_33
  · exact m23198_34
  · exact m23198_40
  · exact m23198_129
  · exact m23198_130
  · exact m23198_136
  · exact m23198_160

def b23199 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 84 74 185 169 233 169 425), lower := (rows 289 38 84 74 16 32 64 128 256), losses := [] }

theorem u23199 : Upper (D 8) (R 8) [288,36,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23199 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23200_3 : Upper (D 8) (R 8) [288,36,80,96,3] 13 :=
  permutation_upper _ _ _ [288,5,40,66,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17165

theorem m23200_9 : Upper (D 8) (R 8) [288,36,80,96,9] 13 :=
  permutation_upper _ _ _ [288,5,96,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17346

theorem m23200_10 : Upper (D 8) (R 8) [288,36,80,96,10] 13 :=
  permutation_upper _ _ _ [288,12,48,96,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17478

theorem m23200_129 : Upper (D 8) (R 8) [288,36,80,96,129] 13 :=
  permutation_upper _ _ _ [288,36,72,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17701

theorem m23200_130 : Upper (D 8) (R 8) [288,36,80,96,130] 13 :=
  permutation_upper _ _ _ [288,36,72,130,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17707

theorem m23200_136 : Upper (D 8) (R 8) [288,36,80,96,136] 13 :=
  permutation_upper _ _ _ [288,36,72,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17713

def r23200 : Route 9 := (fun mask => (mask,id))

def c23200 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23200 : Upper (D 8) (R 8) [288,36,80,96] 13 := by
  apply FastRouting.sound _ _ [288,36,80,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r23200 c23200
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23200_3
  · exact m23200_9
  · exact m23200_10
  · exact m23200_129
  · exact m23200_130
  · exact m23200_136

theorem m23201_3 : Upper (D 8) (R 8) [288,36,80,129,3] 13 :=
  permutation_upper _ _ _ [288,5,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17166

theorem m23201_9 : Upper (D 8) (R 8) [288,36,80,129,9] 13 :=
  permutation_upper _ _ _ [288,5,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17202

theorem m23201_10 : Upper (D 8) (R 8) [288,36,80,129,10] 13 :=
  permutation_upper _ _ _ [288,12,48,65,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17468

theorem m23201_33 : Upper (D 8) (R 8) [288,36,80,129,33] 13 :=
  permutation_upper _ _ _ [288,33,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17590

theorem m23201_34 : Upper (D 8) (R 8) [288,36,80,129,34] 13 :=
  permutation_upper _ _ _ [288,36,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17630

theorem m23201_40 : Upper (D 8) (R 8) [288,36,80,129,40] 13 :=
  permutation_upper _ _ _ [288,36,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17640

theorem m23201_65 : Upper (D 8) (R 8) [288,36,80,129,65] 13 :=
  permutation_upper _ _ _ [288,36,72,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17689

theorem m23201_66 : Upper (D 8) (R 8) [288,36,80,129,66] 13 :=
  permutation_upper _ _ _ [288,36,72,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17692

theorem m23201_72 : Upper (D 8) (R 8) [288,36,80,129,72] 13 :=
  permutation_upper _ _ _ [288,36,72,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17694

theorem m23201_96 : Upper (D 8) (R 8) [288,36,80,129,96] 13 :=
  permutation_upper _ _ _ [288,36,72,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17697

theorem m23201_129 : Upper (D 8) (R 8) [288,36,80,129,129] 13 :=
  permutation_upper _ _ _ [288,36,72,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17702

theorem m23201_130 : Upper (D 8) (R 8) [288,36,80,129,130] 13 :=
  permutation_upper _ _ _ [288,36,72,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17708

theorem m23201_136 : Upper (D 8) (R 8) [288,36,80,129,136] 13 :=
  permutation_upper _ _ _ [288,36,72,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17714

theorem m23201_160 : Upper (D 8) (R 8) [288,36,80,129,160] 13 :=
  permutation_upper _ _ _ [288,36,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17720

theorem m23201_192 : Upper (D 8) (R 8) [288,36,80,129,192] 13 :=
  permutation_upper _ _ _ [288,36,72,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17723

def r23201 : Route 9 := (fun mask => (mask,id))

def c23201 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23201 : Upper (D 8) (R 8) [288,36,80,129] 13 := by
  apply FastRouting.sound _ _ [288,36,80,129] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r23201 c23201
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23201_3
  · exact m23201_9
  · exact m23201_10
  · exact m23201_33
  · exact m23201_34
  · exact m23201_40
  · exact m23201_65
  · exact m23201_66
  · exact m23201_72
  · exact m23201_96
  · exact m23201_129
  · exact m23201_130
  · exact m23201_136
  · exact m23201_160
  · exact m23201_192

theorem m23202_9 : Upper (D 8) (R 8) [288,36,80,130,9] 13 :=
  permutation_upper _ _ _ [288,5,72,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17274

theorem m23202_33 : Upper (D 8) (R 8) [288,36,80,130,33] 13 :=
  permutation_upper _ _ _ [288,33,40,66,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17591

theorem m23202_40 : Upper (D 8) (R 8) [288,36,80,130,40] 13 :=
  permutation_upper _ _ _ [288,36,72,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17687

theorem m23202_65 : Upper (D 8) (R 8) [288,36,80,130,65] 13 :=
  permutation_upper _ _ _ [288,36,72,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17690

theorem m23202_72 : Upper (D 8) (R 8) [288,36,80,130,72] 13 :=
  permutation_upper _ _ _ [288,36,72,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17695

theorem m23202_96 : Upper (D 8) (R 8) [288,36,80,130,96] 13 :=
  permutation_upper _ _ _ [288,36,72,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17698

theorem m23202_129 : Upper (D 8) (R 8) [288,36,80,130,129] 13 :=
  permutation_upper _ _ _ [288,36,72,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17703

theorem m23202_136 : Upper (D 8) (R 8) [288,36,80,130,136] 13 :=
  permutation_upper _ _ _ [288,36,72,144,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17715

theorem m23202_160 : Upper (D 8) (R 8) [288,36,80,130,160] 13 :=
  permutation_upper _ _ _ [288,36,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17721

theorem m23202_192 : Upper (D 8) (R 8) [288,36,80,130,192] 13 :=
  permutation_upper _ _ _ [288,36,72,192,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17724

def r23202 : Route 9 := (fun mask => (mask,id))

def c23202 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23202 : Upper (D 8) (R 8) [288,36,80,130] 13 := by
  apply FastRouting.sound _ _ [288,36,80,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r23202 c23202
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23202_9
  · exact m23202_33
  · exact m23202_40
  · exact m23202_65
  · exact m23202_72
  · exact m23202_96
  · exact m23202_129
  · exact m23202_136
  · exact m23202_160
  · exact m23202_192

theorem m23203_3 : Upper (D 8) (R 8) [288,36,80,160,3] 13 :=
  permutation_upper _ _ _ [288,5,40,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17167

theorem m23203_9 : Upper (D 8) (R 8) [288,36,80,160,9] 13 :=
  permutation_upper _ _ _ [288,5,96,48,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17349

theorem m23203_10 : Upper (D 8) (R 8) [288,36,80,160,10] 13 :=
  permutation_upper _ _ _ [288,12,48,96,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17480

theorem m23203_65 : Upper (D 8) (R 8) [288,36,80,160,65] 13 :=
  permutation_upper _ _ _ [288,36,72,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17691

theorem m23203_66 : Upper (D 8) (R 8) [288,36,80,160,66] 13 :=
  permutation_upper _ _ _ [288,36,72,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17693

theorem m23203_72 : Upper (D 8) (R 8) [288,36,80,160,72] 13 :=
  permutation_upper _ _ _ [288,36,72,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17696

theorem m23203_129 : Upper (D 8) (R 8) [288,36,80,160,129] 13 :=
  permutation_upper _ _ _ [288,36,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17704

theorem m23203_130 : Upper (D 8) (R 8) [288,36,80,160,130] 13 :=
  permutation_upper _ _ _ [288,36,72,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17709

theorem m23203_136 : Upper (D 8) (R 8) [288,36,80,160,136] 13 :=
  permutation_upper _ _ _ [288,36,72,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17716

theorem m23203_192 : Upper (D 8) (R 8) [288,36,80,160,192] 13 :=
  permutation_upper _ _ _ [288,36,72,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17725

def r23203 : Route 9 := (fun mask => (mask,id))

def c23203 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23203 : Upper (D 8) (R 8) [288,36,80,160] 13 := by
  apply FastRouting.sound _ _ [288,36,80,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r23203 c23203
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23203_3
  · exact m23203_9
  · exact m23203_10
  · exact m23203_65
  · exact m23203_66
  · exact m23203_72
  · exact m23203_129
  · exact m23203_130
  · exact m23203_136
  · exact m23203_192

theorem m23204_3 : Upper (D 8) (R 8) [288,36,80,192,3] 13 :=
  permutation_upper _ _ _ [288,5,40,66,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17168

theorem m23204_9 : Upper (D 8) (R 8) [288,36,80,192,9] 13 :=
  permutation_upper _ _ _ [288,5,192,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17394

theorem m23204_10 : Upper (D 8) (R 8) [288,36,80,192,10] 13 :=
  permutation_upper _ _ _ [288,12,48,192,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17485

theorem m23204_33 : Upper (D 8) (R 8) [288,36,80,192,33] 13 :=
  permutation_upper _ _ _ [288,33,40,66,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17592

theorem m23204_34 : Upper (D 8) (R 8) [288,36,80,192,34] 13 :=
  permutation_upper _ _ _ [288,36,40,66,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17631

theorem m23204_40 : Upper (D 8) (R 8) [288,36,80,192,40] 13 :=
  permutation_upper _ _ _ [288,36,72,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17688

theorem m23204_129 : Upper (D 8) (R 8) [288,36,80,192,129] 13 :=
  permutation_upper _ _ _ [288,36,72,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17705

theorem m23204_130 : Upper (D 8) (R 8) [288,36,80,192,130] 13 :=
  permutation_upper _ _ _ [288,36,72,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17710

theorem m23204_136 : Upper (D 8) (R 8) [288,36,80,192,136] 13 :=
  permutation_upper _ _ _ [288,36,72,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17717

theorem m23204_160 : Upper (D 8) (R 8) [288,36,80,192,160] 13 :=
  permutation_upper _ _ _ [288,36,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17722

def r23204 : Route 9 := (fun mask => (mask,id))

def c23204 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23204 : Upper (D 8) (R 8) [288,36,80,192] 13 := by
  apply FastRouting.sound _ _ [288,36,80,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23204 c23204
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23204_3
  · exact m23204_9
  · exact m23204_10
  · exact m23204_33
  · exact m23204_34
  · exact m23204_40
  · exact m23204_129
  · exact m23204_130
  · exact m23204_136
  · exact m23204_160

def b23205 : PairBound 9 := { available := 155, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 73 155 187 219 155 411), lower := (rows 289 38 100 73 16 32 64 128 256), losses := [] }

theorem u23205 : Upper (D 8) (R 8) [288,36,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23206 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 74 153 185 217 153 409), lower := (rows 289 38 100 74 16 32 64 128 256), losses := [] }

theorem u23206 : Upper (D 8) (R 8) [288,36,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23207 : PairBound 9 := { available := 219, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 137 219 251 219 219 475), lower := (rows 289 38 100 137 16 32 64 128 256), losses := [] }

theorem u23207 : Upper (D 8) (R 8) [288,36,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23208 : PairBound 9 := { available := 217, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 138 217 249 217 217 473), lower := (rows 289 38 100 138 16 32 64 128 256), losses := [] }

theorem u23208 : Upper (D 8) (R 8) [288,36,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23209 : PairBound 9 := { available := 155, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 289 38 100 200 155 187 219 155 411), lower := (rows 289 38 100 200 16 32 64 128 256), losses := [] }

theorem u23209 : Upper (D 8) (R 8) [288,36,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23210_3 : Upper (D 8) (R 8) [288,36,192,48,3] 13 :=
  permutation_upper _ _ _ [288,5,40,192,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17184

theorem m23210_9 : Upper (D 8) (R 8) [288,36,192,48,9] 13 :=
  permutation_upper _ _ _ [288,5,34,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17134

theorem m23210_10 : Upper (D 8) (R 8) [288,36,192,48,10] 13 :=
  permutation_upper _ _ _ [288,12,34,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17442

theorem m23210_65 : Upper (D 8) (R 8) [288,36,192,48,65] 13 :=
  permutation_upper _ _ _ [288,36,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17642

theorem m23210_66 : Upper (D 8) (R 8) [288,36,192,48,66] 13 :=
  permutation_upper _ _ _ [288,36,72,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17688

theorem m23210_72 : Upper (D 8) (R 8) [288,36,192,48,72] 13 :=
  permutation_upper _ _ _ [288,36,66,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17669

def r23210 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c23210 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23210 : Upper (D 8) (R 8) [288,36,192,48] 13 := by
  apply FastRouting.sound _ _ [288,36,192,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,192] r23210 c23210
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23210_3
  · exact m23210_9
  · exact m23210_10
  · exact m23210_65
  · exact m23210_66
  · exact m23210_72
  · exact u17737

theorem m23211_3 : Upper (D 8) (R 8) [288,36,192,65,3] 13 :=
  permutation_upper _ _ _ [288,5,40,192,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17185

theorem m23211_9 : Upper (D 8) (R 8) [288,36,192,65,9] 13 :=
  permutation_upper _ _ _ [288,5,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17204

theorem m23211_10 : Upper (D 8) (R 8) [288,36,192,65,10] 13 :=
  permutation_upper _ _ _ [288,12,48,65,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17470

theorem m23211_33 : Upper (D 8) (R 8) [288,36,192,65,33] 13 :=
  permutation_upper _ _ _ [288,33,40,192,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17598

theorem m23211_34 : Upper (D 8) (R 8) [288,36,192,65,34] 13 :=
  permutation_upper _ _ _ [288,36,40,192,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17634

theorem m23211_40 : Upper (D 8) (R 8) [288,36,192,65,40] 13 :=
  permutation_upper _ _ _ [288,36,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17642

def r23211 : Route 9 := (fun mask => (mask,id))

def c23211 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23211 : Upper (D 8) (R 8) [288,36,192,65] 13 := by
  apply FastRouting.sound _ _ [288,36,192,65] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23211 c23211
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23211_3
  · exact m23211_9
  · exact m23211_10
  · exact m23211_33
  · exact m23211_34
  · exact m23211_40
  · exact u17738
  · exact u17739
  · exact u17740
  · exact u17741

def b23212 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 196 74 185 185 249 185 441), lower := (rows 289 38 196 74 16 32 64 128 256), losses := [] }

theorem u23212 : Upper (D 8) (R 8) [288,36,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23213_3 : Upper (D 8) (R 8) [288,36,192,80,3] 13 :=
  permutation_upper _ _ _ [288,5,40,192,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17186

theorem m23213_9 : Upper (D 8) (R 8) [288,36,192,80,9] 13 :=
  permutation_upper _ _ _ [288,5,66,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17230

theorem m23213_10 : Upper (D 8) (R 8) [288,36,192,80,10] 13 :=
  permutation_upper _ _ _ [288,12,48,66,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17476

theorem m23213_33 : Upper (D 8) (R 8) [288,36,192,80,33] 13 :=
  permutation_upper _ _ _ [288,33,40,192,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17599

theorem m23213_34 : Upper (D 8) (R 8) [288,36,192,80,34] 13 :=
  permutation_upper _ _ _ [288,36,40,192,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17635

theorem m23213_40 : Upper (D 8) (R 8) [288,36,192,80,40] 13 :=
  permutation_upper _ _ _ [288,36,66,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17669

theorem m23213_129 : Upper (D 8) (R 8) [288,36,192,80,129] 13 :=
  permutation_upper _ _ _ [288,36,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17740

theorem m23213_130 : Upper (D 8) (R 8) [288,36,192,80,130] 13 :=
  permutation_upper _ _ _ [288,36,192,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17742

def r23213 : Route 9 := (fun mask => (mask,id))

def c23213 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23213 : Upper (D 8) (R 8) [288,36,192,80] 13 := by
  apply FastRouting.sound _ _ [288,36,192,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r23213 c23213
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23213_3
  · exact m23213_9
  · exact m23213_10
  · exact m23213_33
  · exact m23213_34
  · exact m23213_40
  · exact m23213_129
  · exact m23213_130
  · exact u17744
  · exact u17745

theorem m23214_3 : Upper (D 8) (R 8) [288,36,192,96,3] 13 :=
  permutation_upper _ _ _ [288,5,40,192,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17187

theorem m23214_9 : Upper (D 8) (R 8) [288,36,192,96,9] 13 :=
  permutation_upper _ _ _ [288,5,96,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17351

theorem m23214_10 : Upper (D 8) (R 8) [288,36,192,96,10] 13 :=
  permutation_upper _ _ _ [288,12,48,96,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17481

theorem m23214_129 : Upper (D 8) (R 8) [288,36,192,96,129] 13 :=
  permutation_upper _ _ _ [288,36,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17741

theorem m23214_130 : Upper (D 8) (R 8) [288,36,192,96,130] 13 :=
  permutation_upper _ _ _ [288,36,192,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17743

theorem m23214_136 : Upper (D 8) (R 8) [288,36,192,96,136] 13 :=
  permutation_upper _ _ _ [288,36,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17745

def r23214 : Route 9 := (fun mask => (mask,id))

def c23214 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23214 : Upper (D 8) (R 8) [288,36,192,96] 13 := by
  apply FastRouting.sound _ _ [288,36,192,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r23214 c23214
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23214_3
  · exact m23214_9
  · exact m23214_10
  · exact m23214_129
  · exact m23214_130
  · exact m23214_136

def b23215 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 289 38 196 200 59 59 123 187 315), lower := (rows 289 38 196 200 16 32 64 128 256), losses := [] }

theorem u23215 : Upper (D 8) (R 8) [288,36,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m23216_5 : Upper (D 8) (R 8) [288,48,65,66,5] 13 :=
  permutation_upper _ _ _ [288,5,65,34,72] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17195

theorem m23216_9 : Upper (D 8) (R 8) [288,48,65,66,9] 13 :=
  permutation_upper _ _ _ [288,5,72,34,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17263

theorem m23216_12 : Upper (D 8) (R 8) [288,48,65,66,12] 13 :=
  permutation_upper _ _ _ [288,12,65,80,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17493

theorem m23216_33 : Upper (D 8) (R 8) [288,48,65,66,33] 13 :=
  permutation_upper _ _ _ [288,33,34,65,68] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17578

theorem m23216_36 : Upper (D 8) (R 8) [288,48,65,66,36] 13 :=
  permutation_upper _ _ _ [288,36,40,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17625

theorem m23216_40 : Upper (D 8) (R 8) [288,48,65,66,40] 13 :=
  permutation_upper _ _ _ [288,36,40,66,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17629

theorem m23216_129 : Upper (D 8) (R 8) [288,48,65,66,129] 13 :=
  permutation_upper _ _ _ [288,36,65,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17656

theorem m23216_132 : Upper (D 8) (R 8) [288,48,65,66,132] 13 :=
  permutation_upper _ _ _ [288,36,72,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17703

theorem m23216_136 : Upper (D 8) (R 8) [288,48,65,66,136] 13 :=
  permutation_upper _ _ _ [288,36,72,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17708

theorem m23216_160 : Upper (D 8) (R 8) [288,48,65,66,160] 13 :=
  permutation_upper _ _ _ [288,36,96,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17734

def r23216 : Route 9 := (fun mask => (mask,id))

def c23216 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23216 : Upper (D 8) (R 8) [288,48,65,66] 13 := by
  apply FastRouting.sound _ _ [288,48,65,66] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r23216 c23216
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23216_5
  · exact m23216_9
  · exact m23216_12
  · exact m23216_33
  · exact m23216_36
  · exact m23216_40
  · exact m23216_129
  · exact m23216_132
  · exact m23216_136
  · exact m23216_160

theorem m23217_3 : Upper (D 8) (R 8) [288,48,65,96,3] 13 :=
  permutation_upper _ _ _ [288,5,34,65,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17135

theorem m23217_5 : Upper (D 8) (R 8) [288,48,65,96,5] 13 :=
  permutation_upper _ _ _ [288,5,65,34,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17196

theorem m23217_6 : Upper (D 8) (R 8) [288,48,65,96,6] 13 :=
  permutation_upper _ _ _ [288,12,34,65,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17445

theorem m23217_9 : Upper (D 8) (R 8) [288,48,65,96,9] 13 :=
  permutation_upper _ _ _ [288,5,96,34,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17340

theorem m23217_10 : Upper (D 8) (R 8) [288,48,65,96,10] 13 :=
  permutation_upper _ _ _ [288,12,34,96,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17455

theorem m23217_12 : Upper (D 8) (R 8) [288,48,65,96,12] 13 :=
  permutation_upper _ _ _ [288,12,65,96,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17497

theorem m23217_129 : Upper (D 8) (R 8) [288,48,65,96,129] 13 :=
  permutation_upper _ _ _ [288,36,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17658

theorem m23217_130 : Upper (D 8) (R 8) [288,48,65,96,130] 13 :=
  permutation_upper _ _ _ [288,36,66,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17680

theorem m23217_132 : Upper (D 8) (R 8) [288,48,65,96,132] 13 :=
  permutation_upper _ _ _ [288,36,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17704

theorem m23217_136 : Upper (D 8) (R 8) [288,48,65,96,136] 13 :=
  permutation_upper _ _ _ [288,36,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17720

def r23217 : Route 9 := (fun mask => (mask,id))

def c23217 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 257 => 8 | 34 => 5 | 66 => 6 | 258 => 8 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u23217 : Upper (D 8) (R 8) [288,48,65,96] 13 := by
  apply FastRouting.sound _ _ [288,48,65,96] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136] r23217 c23217
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23217_3
  · exact m23217_5
  · exact m23217_6
  · exact m23217_9
  · exact m23217_10
  · exact m23217_12
  · exact m23217_129
  · exact m23217_130
  · exact m23217_132
  · exact m23217_136

theorem m23218_6 : Upper (D 8) (R 8) [288,48,65,129,6] 13 :=
  permutation_upper _ _ _ [288,12,34,65,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17446

theorem m23218_10 : Upper (D 8) (R 8) [288,48,65,129,10] 13 :=
  permutation_upper _ _ _ [288,12,34,65,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17446

theorem m23218_12 : Upper (D 8) (R 8) [288,48,65,129,12] 13 :=
  permutation_upper _ _ _ [288,12,65,129,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17501

theorem m23218_34 : Upper (D 8) (R 8) [288,48,65,129,34] 13 :=
  permutation_upper _ _ _ [288,36,34,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17621

theorem m23218_36 : Upper (D 8) (R 8) [288,48,65,129,36] 13 :=
  permutation_upper _ _ _ [288,36,40,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17626

theorem m23218_40 : Upper (D 8) (R 8) [288,48,65,129,40] 13 :=
  permutation_upper _ _ _ [288,36,40,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17626

theorem m23218_66 : Upper (D 8) (R 8) [288,48,65,129,66] 13 :=
  permutation_upper _ _ _ [288,36,66,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17670

theorem m23218_68 : Upper (D 8) (R 8) [288,48,65,129,68] 13 :=
  permutation_upper _ _ _ [288,36,72,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17689

theorem m23218_72 : Upper (D 8) (R 8) [288,48,65,129,72] 13 :=
  permutation_upper _ _ _ [288,36,72,129,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17699

theorem m23218_96 : Upper (D 8) (R 8) [288,48,65,129,96] 13 :=
  permutation_upper _ _ _ [288,36,96,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17726

theorem m23218_130 : Upper (D 8) (R 8) [288,48,65,129,130] 13 :=
  permutation_upper _ _ _ [288,36,66,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17670

theorem m23218_132 : Upper (D 8) (R 8) [288,48,65,129,132] 13 :=
  permutation_upper _ _ _ [288,36,72,129,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17699

theorem m23218_136 : Upper (D 8) (R 8) [288,48,65,129,136] 13 :=
  permutation_upper _ _ _ [288,36,72,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17689

theorem m23218_160 : Upper (D 8) (R 8) [288,48,65,129,160] 13 :=
  permutation_upper _ _ _ [288,36,96,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17726

theorem m23218_192 : Upper (D 8) (R 8) [288,48,65,129,192] 13 :=
  permutation_upper _ _ _ [288,36,192,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17738

def r23218 : Route 9 := (fun mask => (mask,id))

def c23218 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23218 : Upper (D 8) (R 8) [288,48,65,129] 13 := by
  apply FastRouting.sound _ _ [288,48,65,129] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96,130,132,136,160,192] r23218 c23218
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23218_6
  · exact m23218_10
  · exact m23218_12
  · exact m23218_34
  · exact m23218_36
  · exact m23218_40
  · exact m23218_66
  · exact m23218_68
  · exact m23218_72
  · exact m23218_96
  · exact m23218_130
  · exact m23218_132
  · exact m23218_136
  · exact m23218_160
  · exact m23218_192

theorem m23219_5 : Upper (D 8) (R 8) [288,48,65,130,5] 13 :=
  permutation_upper _ _ _ [288,5,65,34,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17197

theorem m23219_9 : Upper (D 8) (R 8) [288,48,65,130,9] 13 :=
  permutation_upper _ _ _ [288,5,72,34,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17265

theorem m23219_12 : Upper (D 8) (R 8) [288,48,65,130,12] 13 :=
  permutation_upper _ _ _ [288,12,65,144,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17512

theorem m23219_33 : Upper (D 8) (R 8) [288,48,65,130,33] 13 :=
  permutation_upper _ _ _ [288,33,34,65,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17579

theorem m23219_36 : Upper (D 8) (R 8) [288,48,65,130,36] 13 :=
  permutation_upper _ _ _ [288,36,40,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17627

theorem m23219_40 : Upper (D 8) (R 8) [288,48,65,130,40] 13 :=
  permutation_upper _ _ _ [288,36,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17630

theorem m23219_65 : Upper (D 8) (R 8) [288,48,65,130,65] 13 :=
  permutation_upper _ _ _ [288,36,65,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17643

theorem m23219_68 : Upper (D 8) (R 8) [288,48,65,130,68] 13 :=
  permutation_upper _ _ _ [288,36,72,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17690

theorem m23219_72 : Upper (D 8) (R 8) [288,48,65,130,72] 13 :=
  permutation_upper _ _ _ [288,36,72,130,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17706

theorem m23219_96 : Upper (D 8) (R 8) [288,48,65,130,96] 13 :=
  permutation_upper _ _ _ [288,36,96,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17727

theorem m23219_129 : Upper (D 8) (R 8) [288,48,65,130,129] 13 :=
  permutation_upper _ _ _ [288,36,65,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17646

theorem m23219_132 : Upper (D 8) (R 8) [288,48,65,130,132] 13 :=
  permutation_upper _ _ _ [288,36,72,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17700

theorem m23219_136 : Upper (D 8) (R 8) [288,48,65,130,136] 13 :=
  permutation_upper _ _ _ [288,36,72,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17692

theorem m23219_160 : Upper (D 8) (R 8) [288,48,65,130,160] 13 :=
  permutation_upper _ _ _ [288,36,96,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17729

theorem m23219_192 : Upper (D 8) (R 8) [288,48,65,130,192] 13 :=
  permutation_upper _ _ _ [288,36,192,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u17739

def r23219 : Route 9 := (fun mask => (mask,id))

def c23219 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u23219 : Upper (D 8) (R 8) [288,48,65,130] 13 := by
  apply FastRouting.sound _ _ [288,48,65,130] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,129,132,136,160,192] r23219 c23219
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m23219_5
  · exact m23219_9
  · exact m23219_12
  · exact m23219_33
  · exact m23219_36
  · exact m23219_40
  · exact m23219_65
  · exact m23219_68
  · exact m23219_72
  · exact m23219_96
  · exact m23219_129
  · exact m23219_132
  · exact m23219_136
  · exact m23219_160
  · exact m23219_192

#print axioms u23219
end Delivery.IrregularNine14.P08
