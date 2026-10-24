import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0367
import IrregularNine14P08C0368
import IrregularNine14P08C0369
import IrregularNine14P08C0370
import IrregularNine14P08C0371
import IrregularNine14P08C0372
import IrregularNine14P08C0373
import IrregularNine14P08C0374
import IrregularNine14P08C0375
import IrregularNine14P08C0376
import IrregularNine14P08C0377
import IrregularNine14P08C0378
import IrregularNine14P08C0379
import IrregularNine14P08C0380

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m24420_3 : Upper (D 8) (R 8) [192,96,288,3] 13 :=
  permutation_upper _ _ _ [192,5,96,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22062

theorem m24420_5 : Upper (D 8) (R 8) [192,96,288,5] 13 :=
  permutation_upper _ _ _ [192,5,288,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22103

theorem m24420_6 : Upper (D 8) (R 8) [192,96,288,6] 13 :=
  permutation_upper _ _ _ [192,12,96,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22176

theorem m24420_17 : Upper (D 8) (R 8) [192,96,288,17] 13 :=
  permutation_upper _ _ _ [192,17,96,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22216

theorem m24420_18 : Upper (D 8) (R 8) [192,96,288,18] 13 :=
  permutation_upper _ _ _ [192,20,96,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22266

theorem m24420_20 : Upper (D 8) (R 8) [192,96,288,20] 13 :=
  permutation_upper _ _ _ [192,20,288,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22286

theorem m24420_33 : Upper (D 8) (R 8) [192,96,288,33] 13 :=
  permutation_upper _ _ _ [192,33,96,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22361

theorem m24420_34 : Upper (D 8) (R 8) [192,96,288,34] 13 :=
  permutation_upper _ _ _ [192,36,96,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22413

theorem m24420_36 : Upper (D 8) (R 8) [192,96,288,36] 13 :=
  permutation_upper _ _ _ [192,36,288,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22438

theorem m24420_48 : Upper (D 8) (R 8) [192,96,288,48] 13 :=
  permutation_upper _ _ _ [192,48,96,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22459

theorem m24420_129 : Upper (D 8) (R 8) [192,96,288,129] 13 :=
  permutation_upper _ _ _ [192,65,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22470

theorem m24420_130 : Upper (D 8) (R 8) [192,96,288,130] 13 :=
  permutation_upper _ _ _ [192,68,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22483

theorem m24420_132 : Upper (D 8) (R 8) [192,96,288,132] 13 :=
  permutation_upper _ _ _ [192,68,288,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22491

theorem m24420_144 : Upper (D 8) (R 8) [192,96,288,144] 13 :=
  permutation_upper _ _ _ [192,80,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22495

theorem m24420_160 : Upper (D 8) (R 8) [192,96,288,160] 13 :=
  permutation_upper _ _ _ [192,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22499

def r24420 : Route 9 := (fun mask => (mask,id))

def c24420 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 257 => 8 | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u24420 : Upper (D 8) (R 8) [192,96,288] 13 := by
  apply FastRouting.sound _ _ [192,96,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,129,130,132,144,160] r24420 c24420
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24420_3
  · exact m24420_5
  · exact m24420_6
  · exact m24420_17
  · exact m24420_18
  · exact m24420_20
  · exact m24420_33
  · exact m24420_34
  · exact m24420_36
  · exact m24420_48
  · exact m24420_129
  · exact m24420_130
  · exact m24420_132
  · exact m24420_144
  · exact m24420_160

theorem m24421_3 : Upper (D 8) (R 8) [192,96,384,3] 13 :=
  permutation_upper _ _ _ [192,5,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22063

theorem m24421_5 : Upper (D 8) (R 8) [192,96,384,5] 13 :=
  permutation_upper _ _ _ [192,5,320,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22109

theorem m24421_6 : Upper (D 8) (R 8) [192,96,384,6] 13 :=
  permutation_upper _ _ _ [192,12,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22177

theorem m24421_17 : Upper (D 8) (R 8) [192,96,384,17] 13 :=
  permutation_upper _ _ _ [192,17,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22217

theorem m24421_18 : Upper (D 8) (R 8) [192,96,384,18] 13 :=
  permutation_upper _ _ _ [192,20,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22267

theorem m24421_20 : Upper (D 8) (R 8) [192,96,384,20] 13 :=
  permutation_upper _ _ _ [192,20,320,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22290

theorem m24421_33 : Upper (D 8) (R 8) [192,96,384,33] 13 :=
  permutation_upper _ _ _ [192,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22362

theorem m24421_34 : Upper (D 8) (R 8) [192,96,384,34] 13 :=
  permutation_upper _ _ _ [192,36,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22414

theorem m24421_36 : Upper (D 8) (R 8) [192,96,384,36] 13 :=
  permutation_upper _ _ _ [192,36,320,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22443

theorem m24421_48 : Upper (D 8) (R 8) [192,96,384,48] 13 :=
  permutation_upper _ _ _ [192,48,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22460

def r24421 : Route 9 := (fun mask => (mask,id))

def c24421 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u24421 : Upper (D 8) (R 8) [192,96,384] 13 := by
  apply FastRouting.sound _ _ [192,96,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48] r24421 c24421
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24421_3
  · exact m24421_5
  · exact m24421_6
  · exact m24421_17
  · exact m24421_18
  · exact m24421_20
  · exact m24421_33
  · exact m24421_34
  · exact m24421_36
  · exact m24421_48

def b24422 : PairBound 9 := { available := 63, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 194 261 63 63 63 127 191 319), lower := (rows 193 194 261 8 16 32 64 128 256), losses := [] }

theorem u24422 : Upper (D 8) (R 8) [192,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24423 : PairBound 9 := { available := 61, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 194 262 61 61 61 125 189 317), lower := (rows 193 194 262 8 16 32 64 128 256), losses := [] }

theorem u24423 : Upper (D 8) (R 8) [192,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24423 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24424 : PairBound 9 := { available := 63, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 193 194 292 63 63 63 127 191 319), lower := (rows 193 194 292 8 16 32 64 128 256), losses := [] }

theorem u24424 : Upper (D 8) (R 8) [192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24425 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 259 7 13 248 240 240 240 240 496), lower := (rows 259 7 13 8 16 32 64 128 256), losses := [] }

theorem u24425 : Upper (D 8) (R 8) [258,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24426 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24426 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24426 : Upper (D 8) (R 8) [258,5,24] 13 := by
  apply FastRouting.sound _ _ [258,5,24] 13 (by decide) (choices 2) [33,65,96,192] r24426 c24426
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22500
  · exact u22501
  · exact u22502
  · exact u22503

def b24427 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 259 7 37 248 248 248 248 248 504), lower := (rows 259 7 37 8 16 32 64 128 256), losses := [] }

theorem u24427 : Upper (D 8) (R 8) [258,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24428 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24428 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24428 : Upper (D 8) (R 8) [258,5,40] 13 := by
  apply FastRouting.sound _ _ [258,5,40] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r24428 c24428
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22504
  · exact u22505
  · exact u22506
  · exact u22507
  · exact u22508
  · exact u22509
  · exact u22510

def b24429 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 259 7 69 248 248 248 248 248 504), lower := (rows 259 7 69 8 16 32 64 128 256), losses := [] }

theorem u24429 : Upper (D 8) (R 8) [258,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24430 : Route 9 := (fun mask => (mask,id))

def c24430 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24430 : Upper (D 8) (R 8) [258,5,72] 13 := by
  apply FastRouting.sound _ _ [258,5,72] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24430 c24430
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22511
  · exact u22512
  · exact u22513
  · exact u22514
  · exact u22515
  · exact u22516
  · exact u22517
  · exact u22518
  · exact u22519
  · exact u22520

def r24431 : Route 9 := (fun mask => (mask,id))

def c24431 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24431 : Upper (D 8) (R 8) [258,5,96] 13 := by
  apply FastRouting.sound _ _ [258,5,96] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24431 c24431
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22521
  · exact u22522
  · exact u22523
  · exact u22524
  · exact u22525
  · exact u22526
  · exact u22527
  · exact u22528
  · exact u22529
  · exact u22530

def r24432 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24432 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24432 : Upper (D 8) (R 8) [258,5,192] 13 := by
  apply FastRouting.sound _ _ [258,5,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r24432 c24432
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22531
  · exact u22532
  · exact u22533
  · exact u22534
  · exact u22535
  · exact u22536
  · exact u22537

def r24433 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24433 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24433 : Upper (D 8) (R 8) [258,12,17] 13 := by
  apply FastRouting.sound _ _ [258,12,17] 13 (by decide) (choices 2) [33,65,96,192] r24433 c24433
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22538
  · exact u22539
  · exact u22540
  · exact u22541

theorem m24434_17 : Upper (D 8) (R 8) [258,12,33,17] 13 :=
  permutation_upper _ _ _ [258,12,17,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22538

def r24434 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24434 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24434 : Upper (D 8) (R 8) [258,12,33] 13 := by
  apply FastRouting.sound _ _ [258,12,33] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r24434 c24434
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24434_17
  · exact u22542
  · exact u22543
  · exact u22544
  · exact u22545
  · exact u22546
  · exact u22547

theorem m24435_33 : Upper (D 8) (R 8) [258,12,48,33] 13 :=
  permutation_upper _ _ _ [258,12,33,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22543

def r24435 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24435 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24435 : Upper (D 8) (R 8) [258,12,48] 13 := by
  apply FastRouting.sound _ _ [258,12,48] 13 (by decide) (choices 2) [33,65,96,192] r24435 c24435
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m24435_33
  · exact u22548
  · exact u22549
  · exact u22550

theorem m24436_17 : Upper (D 8) (R 8) [258,12,65,17] 13 :=
  permutation_upper _ _ _ [258,12,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22539

theorem m24436_33 : Upper (D 8) (R 8) [258,12,65,33] 13 :=
  permutation_upper _ _ _ [258,12,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22544

theorem m24436_48 : Upper (D 8) (R 8) [258,12,65,48] 13 :=
  permutation_upper _ _ _ [258,12,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22548

def r24436 : Route 9 := (fun mask => (mask,id))

def c24436 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24436 : Upper (D 8) (R 8) [258,12,65] 13 := by
  apply FastRouting.sound _ _ [258,12,65] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24436 c24436
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24436_17
  · exact m24436_33
  · exact m24436_48
  · exact u22551
  · exact u22552
  · exact u22553
  · exact u22554
  · exact u22555
  · exact u22556
  · exact u22557

theorem m24437_33 : Upper (D 8) (R 8) [258,12,80,33] 13 :=
  permutation_upper _ _ _ [258,12,33,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22545

theorem m24437_65 : Upper (D 8) (R 8) [258,12,80,65] 13 :=
  permutation_upper _ _ _ [258,12,65,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22552

theorem m24437_129 : Upper (D 8) (R 8) [258,12,80,129] 13 :=
  permutation_upper _ _ _ [258,12,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22555

def r24437 : Route 9 := (fun mask => (mask,id))

def c24437 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24437 : Upper (D 8) (R 8) [258,12,80] 13 := by
  apply FastRouting.sound _ _ [258,12,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r24437 c24437
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24437_33
  · exact m24437_65
  · exact u22558
  · exact m24437_129
  · exact u22559
  · exact u22560

theorem m24438_17 : Upper (D 8) (R 8) [258,12,96,17] 13 :=
  permutation_upper _ _ _ [258,12,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22540

theorem m24438_33 : Upper (D 8) (R 8) [258,12,96,33] 13 :=
  permutation_upper _ _ _ [258,12,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22546

theorem m24438_48 : Upper (D 8) (R 8) [258,12,96,48] 13 :=
  permutation_upper _ _ _ [258,12,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22549

theorem m24438_65 : Upper (D 8) (R 8) [258,12,96,65] 13 :=
  permutation_upper _ _ _ [258,12,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22553

theorem m24438_80 : Upper (D 8) (R 8) [258,12,96,80] 13 :=
  permutation_upper _ _ _ [258,12,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22558

theorem m24438_129 : Upper (D 8) (R 8) [258,12,96,129] 13 :=
  permutation_upper _ _ _ [258,12,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22556

theorem m24438_144 : Upper (D 8) (R 8) [258,12,96,144] 13 :=
  permutation_upper _ _ _ [258,12,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22559

def r24438 : Route 9 := (fun mask => (mask,id))

def c24438 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24438 : Upper (D 8) (R 8) [258,12,96] 13 := by
  apply FastRouting.sound _ _ [258,12,96] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24438 c24438
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24438_17
  · exact m24438_33
  · exact m24438_48
  · exact m24438_65
  · exact m24438_80
  · exact u22561
  · exact m24438_129
  · exact m24438_144
  · exact u22562
  · exact u22563

theorem m24439_17 : Upper (D 8) (R 8) [258,12,192,17] 13 :=
  permutation_upper _ _ _ [258,12,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22541

theorem m24439_33 : Upper (D 8) (R 8) [258,12,192,33] 13 :=
  permutation_upper _ _ _ [258,12,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22547

theorem m24439_48 : Upper (D 8) (R 8) [258,12,192,48] 13 :=
  permutation_upper _ _ _ [258,12,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22550

theorem m24439_65 : Upper (D 8) (R 8) [258,12,192,65] 13 :=
  permutation_upper _ _ _ [258,12,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22557

theorem m24439_80 : Upper (D 8) (R 8) [258,12,192,80] 13 :=
  permutation_upper _ _ _ [258,12,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22560

theorem m24439_96 : Upper (D 8) (R 8) [258,12,192,96] 13 :=
  permutation_upper _ _ _ [258,12,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22563

def r24439 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24439 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24439 : Upper (D 8) (R 8) [258,12,192] 13 := by
  apply FastRouting.sound _ _ [258,12,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r24439 c24439
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24439_17
  · exact m24439_33
  · exact m24439_48
  · exact m24439_65
  · exact m24439_80
  · exact m24439_96
  · exact u22564

def b24440 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 13 252 244 244 244 244 500), lower := (rows 259 35 13 8 16 32 64 128 256), losses := [] }

theorem u24440 : Upper (D 8) (R 8) [258,33,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24441_5 : Upper (D 8) (R 8) [258,33,24,5] 13 :=
  permutation_upper _ _ _ [258,33,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22565

def r24441 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24441 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24441 : Upper (D 8) (R 8) [258,33,24] 13 := by
  apply FastRouting.sound _ _ [258,33,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,192] r24441 c24441
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24441_5
  · exact u22574
  · exact u22575
  · exact u22576
  · exact u22577
  · exact u22578
  · exact u22579

def b24442 : PairBound 9 := { available := 252, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 259 35 37 252 252 252 252 252 508), lower := (rows 259 35 37 8 16 32 64 128 256), losses := [] }

theorem u24442 : Upper (D 8) (R 8) [258,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24443_5 : Upper (D 8) (R 8) [258,33,40,5] 13 :=
  permutation_upper _ _ _ [258,33,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22566

theorem m24443_17 : Upper (D 8) (R 8) [258,33,40,17] 13 :=
  permutation_upper _ _ _ [258,33,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22570

theorem m24443_20 : Upper (D 8) (R 8) [258,33,40,20] 13 :=
  permutation_upper _ _ _ [258,33,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22575

theorem m24443_33 : Upper (D 8) (R 8) [258,33,40,33] 13 :=
  permutation_upper _ _ _ [258,33,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22580

def r24443 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24443 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24443 : Upper (D 8) (R 8) [258,33,40] 13 := by
  apply FastRouting.sound _ _ [258,33,40] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] r24443 c24443
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24443_5
  · exact m24443_17
  · exact m24443_20
  · exact m24443_33
  · exact u22584
  · exact u22585
  · exact u22586
  · exact u22587
  · exact u22588
  · exact u22589
  · exact u22590

def b24444 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 35 69 252 252 252 252 252 508), lower := (rows 259 35 69 8 16 32 64 128 256), losses := [] }

theorem u24444 : Upper (D 8) (R 8) [258,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24445_5 : Upper (D 8) (R 8) [258,33,72,5] 13 :=
  permutation_upper _ _ _ [258,33,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22567

theorem m24445_17 : Upper (D 8) (R 8) [258,33,72,17] 13 :=
  permutation_upper _ _ _ [258,33,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22571

theorem m24445_20 : Upper (D 8) (R 8) [258,33,72,20] 13 :=
  permutation_upper _ _ _ [258,33,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22577

theorem m24445_33 : Upper (D 8) (R 8) [258,33,72,33] 13 :=
  permutation_upper _ _ _ [258,33,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22581

theorem m24445_36 : Upper (D 8) (R 8) [258,33,72,36] 13 :=
  permutation_upper _ _ _ [258,33,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22587

theorem m24445_48 : Upper (D 8) (R 8) [258,33,72,48] 13 :=
  permutation_upper _ _ _ [258,33,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22591

theorem m24445_65 : Upper (D 8) (R 8) [258,33,72,65] 13 :=
  permutation_upper _ _ _ [258,33,65,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22594

theorem m24445_129 : Upper (D 8) (R 8) [258,33,72,129] 13 :=
  permutation_upper _ _ _ [258,33,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22596

def r24445 : Route 9 := (fun mask => (mask,id))

def c24445 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24445 : Upper (D 8) (R 8) [258,33,72] 13 := by
  apply FastRouting.sound _ _ [258,33,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24445 c24445
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24445_5
  · exact m24445_17
  · exact m24445_20
  · exact m24445_33
  · exact m24445_36
  · exact m24445_48
  · exact m24445_65
  · exact u22599
  · exact u22600
  · exact u22601
  · exact m24445_129
  · exact u22602
  · exact u22603
  · exact u22604
  · exact u22605

theorem m24446_5 : Upper (D 8) (R 8) [258,33,96,5] 13 :=
  permutation_upper _ _ _ [258,33,9,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22568

theorem m24446_17 : Upper (D 8) (R 8) [258,33,96,17] 13 :=
  permutation_upper _ _ _ [258,33,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22572

theorem m24446_20 : Upper (D 8) (R 8) [258,33,96,20] 13 :=
  permutation_upper _ _ _ [258,33,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22578

theorem m24446_33 : Upper (D 8) (R 8) [258,33,96,33] 13 :=
  permutation_upper _ _ _ [258,33,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22582

theorem m24446_36 : Upper (D 8) (R 8) [258,33,96,36] 13 :=
  permutation_upper _ _ _ [258,33,40,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22589

theorem m24446_48 : Upper (D 8) (R 8) [258,33,96,48] 13 :=
  permutation_upper _ _ _ [258,33,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22592

theorem m24446_65 : Upper (D 8) (R 8) [258,33,96,65] 13 :=
  permutation_upper _ _ _ [258,33,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22595

theorem m24446_68 : Upper (D 8) (R 8) [258,33,96,68] 13 :=
  permutation_upper _ _ _ [258,33,72,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22601

theorem m24446_80 : Upper (D 8) (R 8) [258,33,96,80] 13 :=
  permutation_upper _ _ _ [258,33,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22606

theorem m24446_129 : Upper (D 8) (R 8) [258,33,96,129] 13 :=
  permutation_upper _ _ _ [258,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22597

theorem m24446_132 : Upper (D 8) (R 8) [258,33,96,132] 13 :=
  permutation_upper _ _ _ [258,33,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22604

theorem m24446_144 : Upper (D 8) (R 8) [258,33,96,144] 13 :=
  permutation_upper _ _ _ [258,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22607

def r24446 : Route 9 := (fun mask => (mask,id))

def c24446 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24446 : Upper (D 8) (R 8) [258,33,96] 13 := by
  apply FastRouting.sound _ _ [258,33,96] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24446 c24446
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24446_5
  · exact m24446_17
  · exact m24446_20
  · exact m24446_33
  · exact m24446_36
  · exact m24446_48
  · exact m24446_65
  · exact m24446_68
  · exact m24446_80
  · exact u22609
  · exact m24446_129
  · exact m24446_132
  · exact m24446_144
  · exact u22610
  · exact u22611

theorem m24447_5 : Upper (D 8) (R 8) [258,33,192,5] 13 :=
  permutation_upper _ _ _ [258,33,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22569

theorem m24447_17 : Upper (D 8) (R 8) [258,33,192,17] 13 :=
  permutation_upper _ _ _ [258,33,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22573

theorem m24447_20 : Upper (D 8) (R 8) [258,33,192,20] 13 :=
  permutation_upper _ _ _ [258,33,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22579

theorem m24447_33 : Upper (D 8) (R 8) [258,33,192,33] 13 :=
  permutation_upper _ _ _ [258,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22583

theorem m24447_36 : Upper (D 8) (R 8) [258,33,192,36] 13 :=
  permutation_upper _ _ _ [258,33,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22590

theorem m24447_48 : Upper (D 8) (R 8) [258,33,192,48] 13 :=
  permutation_upper _ _ _ [258,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22593

theorem m24447_65 : Upper (D 8) (R 8) [258,33,192,65] 13 :=
  permutation_upper _ _ _ [258,33,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22598

theorem m24447_68 : Upper (D 8) (R 8) [258,33,192,68] 13 :=
  permutation_upper _ _ _ [258,33,72,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22605

theorem m24447_80 : Upper (D 8) (R 8) [258,33,192,80] 13 :=
  permutation_upper _ _ _ [258,33,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22608

theorem m24447_96 : Upper (D 8) (R 8) [258,33,192,96] 13 :=
  permutation_upper _ _ _ [258,33,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22611

def r24447 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24447 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24447 : Upper (D 8) (R 8) [258,33,192] 13 := by
  apply FastRouting.sound _ _ [258,33,192] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,192] r24447 c24447
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24447_5
  · exact m24447_17
  · exact m24447_20
  · exact m24447_33
  · exact m24447_36
  · exact m24447_48
  · exact m24447_65
  · exact m24447_68
  · exact m24447_80
  · exact m24447_96
  · exact u22612

def r24448 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24448 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24448 : Upper (D 8) (R 8) [258,36,9] 13 := by
  apply FastRouting.sound _ _ [258,36,9] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r24448 c24448
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22613
  · exact u22614
  · exact u22615
  · exact u22616
  · exact u22617
  · exact u22618
  · exact u22619

def r24449 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24449 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24449 : Upper (D 8) (R 8) [258,36,24] 13 := by
  apply FastRouting.sound _ _ [258,36,24] 13 (by decide) (choices 2) [33,65,96,192] r24449 c24449
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22620
  · exact u22621
  · exact u22622
  · exact u22623

def b24450 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 37 249 249 249 249 249 505), lower := (rows 259 38 37 8 16 32 64 128 256), losses := [] }

theorem u24450 : Upper (D 8) (R 8) [258,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24451 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 44 249 241 241 241 241 497), lower := (rows 259 38 44 8 16 32 64 128 256), losses := [] }

theorem u24451 : Upper (D 8) (R 8) [258,36,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24452 : Route 9 := (fun mask => (mask,id))

def c24452 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24452 : Upper (D 8) (R 8) [258,36,65] 13 := by
  apply FastRouting.sound _ _ [258,36,65] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24452 c24452
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22624
  · exact u22625
  · exact u22626
  · exact u22627
  · exact u22628
  · exact u22629
  · exact u22630
  · exact u22631
  · exact u22632
  · exact u22633

def r24453 : Route 9 := (fun mask => (mask,id))

def c24453 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24453 : Upper (D 8) (R 8) [258,36,72] 13 := by
  apply FastRouting.sound _ _ [258,36,72] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24453 c24453
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22634
  · exact u22635
  · exact u22636
  · exact u22637
  · exact u22638
  · exact u22639
  · exact u22640
  · exact u22641
  · exact u22642
  · exact u22643

def b24454 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 100 249 249 249 249 249 505), lower := (rows 259 38 100 8 16 32 64 128 256), losses := [] }

theorem u24454 : Upper (D 8) (R 8) [258,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24455 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c24455 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24455 : Upper (D 8) (R 8) [258,36,192] 13 := by
  apply FastRouting.sound _ _ [258,36,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r24455 c24455
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22644
  · exact u22645
  · exact u22646
  · exact u22647
  · exact u22648
  · exact u22649
  · exact u22650

def b24456 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 13 252 244 244 244 244 500), lower := (rows 259 67 13 8 16 32 64 128 256), losses := [] }

theorem u24456 : Upper (D 8) (R 8) [258,65,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24457_5 : Upper (D 8) (R 8) [258,65,24,5] 13 :=
  permutation_upper _ _ _ [258,65,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22651

def r24457 : Route 9 := (fun mask => (mask,id))

def c24457 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24457 : Upper (D 8) (R 8) [258,65,24] 13 := by
  apply FastRouting.sound _ _ [258,65,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r24457 c24457
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24457_5
  · exact u22664
  · exact u22665
  · exact u22666
  · exact u22667
  · exact u22668
  · exact u22669
  · exact u22670
  · exact u22671
  · exact u22672

def b24458 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 252 252 252 252 252 508), lower := (rows 259 67 37 8 16 32 64 128 256), losses := [] }

theorem u24458 : Upper (D 8) (R 8) [258,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24459_5 : Upper (D 8) (R 8) [258,65,40,5] 13 :=
  permutation_upper _ _ _ [258,65,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22652

theorem m24459_17 : Upper (D 8) (R 8) [258,65,40,17] 13 :=
  permutation_upper _ _ _ [258,65,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22658

theorem m24459_20 : Upper (D 8) (R 8) [258,65,40,20] 13 :=
  permutation_upper _ _ _ [258,65,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22665

theorem m24459_33 : Upper (D 8) (R 8) [258,65,40,33] 13 :=
  permutation_upper _ _ _ [258,65,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22673

def r24459 : Route 9 := (fun mask => (mask,id))

def c24459 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24459 : Upper (D 8) (R 8) [258,65,40] 13 := by
  apply FastRouting.sound _ _ [258,65,40] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24459 c24459
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24459_5
  · exact m24459_17
  · exact m24459_20
  · exact m24459_33
  · exact u22679
  · exact u22680
  · exact u22681
  · exact u22682
  · exact u22683
  · exact u22684
  · exact u22685
  · exact u22686
  · exact u22687
  · exact u22688
  · exact u22689

def b24460 : PairBound 9 := { available := 188, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 259 67 69 188 188 188 252 188 444), lower := (rows 259 67 69 8 16 32 64 128 256), losses := [] }

theorem u24460 : Upper (D 8) (R 8) [258,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24461_5 : Upper (D 8) (R 8) [258,65,72,5] 13 :=
  permutation_upper _ _ _ [258,65,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22653

theorem m24461_17 : Upper (D 8) (R 8) [258,65,72,17] 13 :=
  permutation_upper _ _ _ [258,65,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22659

theorem m24461_20 : Upper (D 8) (R 8) [258,65,72,20] 13 :=
  permutation_upper _ _ _ [258,65,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22667

theorem m24461_33 : Upper (D 8) (R 8) [258,65,72,33] 13 :=
  permutation_upper _ _ _ [258,65,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22674

theorem m24461_36 : Upper (D 8) (R 8) [258,65,72,36] 13 :=
  permutation_upper _ _ _ [258,65,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22682

theorem m24461_48 : Upper (D 8) (R 8) [258,65,72,48] 13 :=
  permutation_upper _ _ _ [258,65,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22690

def r24461 : Route 9 := (fun mask => (mask,id))

def c24461 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u24461 : Upper (D 8) (R 8) [258,65,72] 13 := by
  apply FastRouting.sound _ _ [258,65,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r24461 c24461
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24461_5
  · exact m24461_17
  · exact m24461_20
  · exact m24461_33
  · exact m24461_36
  · exact m24461_48
  · exact u22697
  · exact u22698
  · exact u22699
  · exact u22700

theorem m24462_5 : Upper (D 8) (R 8) [258,65,96,5] 13 :=
  permutation_upper _ _ _ [258,65,9,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22654

theorem m24462_17 : Upper (D 8) (R 8) [258,65,96,17] 13 :=
  permutation_upper _ _ _ [258,65,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22660

theorem m24462_20 : Upper (D 8) (R 8) [258,65,96,20] 13 :=
  permutation_upper _ _ _ [258,65,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22668

theorem m24462_33 : Upper (D 8) (R 8) [258,65,96,33] 13 :=
  permutation_upper _ _ _ [258,65,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22675

theorem m24462_36 : Upper (D 8) (R 8) [258,65,96,36] 13 :=
  permutation_upper _ _ _ [258,65,40,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22684

theorem m24462_48 : Upper (D 8) (R 8) [258,65,96,48] 13 :=
  permutation_upper _ _ _ [258,65,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22691

def r24462 : Route 9 := (fun mask => (mask,id))

def c24462 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u24462 : Upper (D 8) (R 8) [258,65,96] 13 := by
  apply FastRouting.sound _ _ [258,65,96] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r24462 c24462
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24462_5
  · exact m24462_17
  · exact m24462_20
  · exact m24462_33
  · exact m24462_36
  · exact m24462_48
  · exact u22703
  · exact u22704
  · exact u22705
  · exact u22706

def b24463 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 120, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 133 252 252 252 252 252 508), lower := (rows 259 67 133 8 16 32 64 128 256), losses := [] }

theorem u24463 : Upper (D 8) (R 8) [258,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m24464_5 : Upper (D 8) (R 8) [258,65,136,5] 13 :=
  permutation_upper _ _ _ [258,65,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22655

theorem m24464_17 : Upper (D 8) (R 8) [258,65,136,17] 13 :=
  permutation_upper _ _ _ [258,65,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22661

theorem m24464_20 : Upper (D 8) (R 8) [258,65,136,20] 13 :=
  permutation_upper _ _ _ [258,65,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22670

theorem m24464_33 : Upper (D 8) (R 8) [258,65,136,33] 13 :=
  permutation_upper _ _ _ [258,65,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22676

theorem m24464_36 : Upper (D 8) (R 8) [258,65,136,36] 13 :=
  permutation_upper _ _ _ [258,65,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22686

theorem m24464_48 : Upper (D 8) (R 8) [258,65,136,48] 13 :=
  permutation_upper _ _ _ [258,65,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22692

theorem m24464_65 : Upper (D 8) (R 8) [258,65,136,65] 13 :=
  permutation_upper _ _ _ [258,65,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22695

theorem m24464_68 : Upper (D 8) (R 8) [258,65,136,68] 13 :=
  permutation_upper _ _ _ [258,65,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22698

theorem m24464_80 : Upper (D 8) (R 8) [258,65,136,80] 13 :=
  permutation_upper _ _ _ [258,65,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22701

theorem m24464_96 : Upper (D 8) (R 8) [258,65,136,96] 13 :=
  permutation_upper _ _ _ [258,65,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22704

theorem m24464_129 : Upper (D 8) (R 8) [258,65,136,129] 13 :=
  permutation_upper _ _ _ [258,65,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22707

def r24464 : Route 9 := (fun mask => (mask,id))

def c24464 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24464 : Upper (D 8) (R 8) [258,65,136] 13 := by
  apply FastRouting.sound _ _ [258,65,136] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24464 c24464
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24464_5
  · exact m24464_17
  · exact m24464_20
  · exact m24464_33
  · exact m24464_36
  · exact m24464_48
  · exact m24464_65
  · exact m24464_68
  · exact m24464_80
  · exact m24464_96
  · exact m24464_129
  · exact u22710
  · exact u22711
  · exact u22712
  · exact u22713

theorem m24465_5 : Upper (D 8) (R 8) [258,65,160,5] 13 :=
  permutation_upper _ _ _ [258,65,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22656

theorem m24465_17 : Upper (D 8) (R 8) [258,65,160,17] 13 :=
  permutation_upper _ _ _ [258,65,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22662

theorem m24465_20 : Upper (D 8) (R 8) [258,65,160,20] 13 :=
  permutation_upper _ _ _ [258,65,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22671

theorem m24465_33 : Upper (D 8) (R 8) [258,65,160,33] 13 :=
  permutation_upper _ _ _ [258,65,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22677

theorem m24465_36 : Upper (D 8) (R 8) [258,65,160,36] 13 :=
  permutation_upper _ _ _ [258,65,40,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22688

theorem m24465_48 : Upper (D 8) (R 8) [258,65,160,48] 13 :=
  permutation_upper _ _ _ [258,65,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22693

theorem m24465_65 : Upper (D 8) (R 8) [258,65,160,65] 13 :=
  permutation_upper _ _ _ [258,65,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22696

theorem m24465_68 : Upper (D 8) (R 8) [258,65,160,68] 13 :=
  permutation_upper _ _ _ [258,65,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22700

theorem m24465_80 : Upper (D 8) (R 8) [258,65,160,80] 13 :=
  permutation_upper _ _ _ [258,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22702

theorem m24465_96 : Upper (D 8) (R 8) [258,65,160,96] 13 :=
  permutation_upper _ _ _ [258,65,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22706

theorem m24465_129 : Upper (D 8) (R 8) [258,65,160,129] 13 :=
  permutation_upper _ _ _ [258,65,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22708

theorem m24465_132 : Upper (D 8) (R 8) [258,65,160,132] 13 :=
  permutation_upper _ _ _ [258,65,136,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22712

theorem m24465_144 : Upper (D 8) (R 8) [258,65,160,144] 13 :=
  permutation_upper _ _ _ [258,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22714

def r24465 : Route 9 := (fun mask => (mask,id))

def c24465 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24465 : Upper (D 8) (R 8) [258,65,160] 13 := by
  apply FastRouting.sound _ _ [258,65,160] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24465 c24465
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24465_5
  · exact m24465_17
  · exact m24465_20
  · exact m24465_33
  · exact m24465_36
  · exact m24465_48
  · exact m24465_65
  · exact m24465_68
  · exact m24465_80
  · exact m24465_96
  · exact m24465_129
  · exact m24465_132
  · exact m24465_144
  · exact u22716
  · exact u22717

theorem m24466_5 : Upper (D 8) (R 8) [258,65,192,5] 13 :=
  permutation_upper _ _ _ [258,65,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22657

theorem m24466_17 : Upper (D 8) (R 8) [258,65,192,17] 13 :=
  permutation_upper _ _ _ [258,65,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22663

theorem m24466_20 : Upper (D 8) (R 8) [258,65,192,20] 13 :=
  permutation_upper _ _ _ [258,65,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22672

theorem m24466_33 : Upper (D 8) (R 8) [258,65,192,33] 13 :=
  permutation_upper _ _ _ [258,65,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22678

theorem m24466_36 : Upper (D 8) (R 8) [258,65,192,36] 13 :=
  permutation_upper _ _ _ [258,65,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22689

theorem m24466_48 : Upper (D 8) (R 8) [258,65,192,48] 13 :=
  permutation_upper _ _ _ [258,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22694

theorem m24466_129 : Upper (D 8) (R 8) [258,65,192,129] 13 :=
  permutation_upper _ _ _ [258,65,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22709

theorem m24466_132 : Upper (D 8) (R 8) [258,65,192,132] 13 :=
  permutation_upper _ _ _ [258,65,136,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22713

theorem m24466_144 : Upper (D 8) (R 8) [258,65,192,144] 13 :=
  permutation_upper _ _ _ [258,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22715

theorem m24466_160 : Upper (D 8) (R 8) [258,65,192,160] 13 :=
  permutation_upper _ _ _ [258,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22717

def r24466 : Route 9 := (fun mask => (mask,id))

def c24466 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u24466 : Upper (D 8) (R 8) [258,65,192] 13 := by
  apply FastRouting.sound _ _ [258,65,192] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160] r24466 c24466
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24466_5
  · exact m24466_17
  · exact m24466_20
  · exact m24466_33
  · exact m24466_36
  · exact m24466_48
  · exact m24466_129
  · exact m24466_132
  · exact m24466_144
  · exact m24466_160

def r24467 : Route 9 := (fun mask => (mask,id))

def c24467 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24467 : Upper (D 8) (R 8) [258,68,9] 13 := by
  apply FastRouting.sound _ _ [258,68,9] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24467 c24467
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22718
  · exact u22719
  · exact u22720
  · exact u22721
  · exact u22722
  · exact u22723
  · exact u22724
  · exact u22725
  · exact u22726
  · exact u22727

def r24468 : Route 9 := (fun mask => (mask,id))

def c24468 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24468 : Upper (D 8) (R 8) [258,68,24] 13 := by
  apply FastRouting.sound _ _ [258,68,24] 13 (by decide) (choices 2) [33,65,96,129,160,192] r24468 c24468
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22728
  · exact u22729
  · exact u22730
  · exact u22731
  · exact u22732
  · exact u22733

def r24469 : Route 9 := (fun mask => (mask,id))

def c24469 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24469 : Upper (D 8) (R 8) [258,68,33] 13 := by
  apply FastRouting.sound _ _ [258,68,33] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24469 c24469
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22734
  · exact u22735
  · exact u22736
  · exact u22737
  · exact u22738
  · exact u22739
  · exact u22740
  · exact u22741
  · exact u22742
  · exact u22743

def r24470 : Route 9 := (fun mask => (mask,id))

def c24470 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24470 : Upper (D 8) (R 8) [258,68,40] 13 := by
  apply FastRouting.sound _ _ [258,68,40] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24470 c24470
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22744
  · exact u22745
  · exact u22746
  · exact u22747
  · exact u22748
  · exact u22749
  · exact u22750
  · exact u22751
  · exact u22752
  · exact u22753

def b24471 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 69 185 185 185 249 185 441), lower := (rows 259 70 69 8 16 32 64 128 256), losses := [] }

theorem u24471 : Upper (D 8) (R 8) [258,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24472 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 76 185 177 177 241 177 433), lower := (rows 259 70 76 8 16 32 64 128 256), losses := [] }

theorem u24472 : Upper (D 8) (R 8) [258,68,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24473 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 100 185 185 185 249 185 441), lower := (rows 259 70 100 8 16 32 64 128 256), losses := [] }

theorem u24473 : Upper (D 8) (R 8) [258,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24474 : Route 9 := (fun mask => (mask,id))

def c24474 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24474 : Upper (D 8) (R 8) [258,68,129] 13 := by
  apply FastRouting.sound _ _ [258,68,129] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24474 c24474
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22754
  · exact u22755
  · exact u22756
  · exact u22757
  · exact u22758
  · exact u22759
  · exact u22760
  · exact u22761
  · exact u22762
  · exact u22763

def r24475 : Route 9 := (fun mask => (mask,id))

def c24475 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24475 : Upper (D 8) (R 8) [258,68,136] 13 := by
  apply FastRouting.sound _ _ [258,68,136] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24475 c24475
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22764
  · exact u22765
  · exact u22766
  · exact u22767
  · exact u22768
  · exact u22769
  · exact u22770
  · exact u22771
  · exact u22772
  · exact u22773

def r24476 : Route 9 := (fun mask => (mask,id))

def c24476 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24476 : Upper (D 8) (R 8) [258,68,160] 13 := by
  apply FastRouting.sound _ _ [258,68,160] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r24476 c24476
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22774
  · exact u22775
  · exact u22776
  · exact u22777
  · exact u22778
  · exact u22779
  · exact u22780
  · exact u22781
  · exact u22782
  · exact u22783

def b24477 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 259 70 196 185 185 185 249 185 441), lower := (rows 259 70 196 8 16 32 64 128 256), losses := [] }

theorem u24477 : Upper (D 8) (R 8) [258,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r24478 : Route 9 := (fun mask => (mask,id))

def c24478 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24478 : Upper (D 8) (R 8) [258,96,9] 13 := by
  apply FastRouting.sound _ _ [258,96,9] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192] r24478 c24478
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u22784
  · exact u22785
  · exact u22786
  · exact u22787
  · exact u22788
  · exact u22789
  · exact u22790
  · exact u22791
  · exact u22792
  · exact u22793
  · exact u22794
  · exact u22795
  · exact u22796
  · exact u22797
  · exact u22798

theorem m24479_5 : Upper (D 8) (R 8) [258,96,24,5] 13 :=
  permutation_upper _ _ _ [258,96,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u22786

def r24479 : Route 9 := (fun mask => (mask,id))

def c24479 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u24479 : Upper (D 8) (R 8) [258,96,24] 13 := by
  apply FastRouting.sound _ _ [258,96,24] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r24479 c24479
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m24479_5
  · exact u22806
  · exact u22807
  · exact u22808
  · exact u22809
  · exact u22810
  · exact u22811
  · exact u22812
  · exact u22813
  · exact u22814

#print axioms u24479
end Delivery.IrregularNine14.P08
