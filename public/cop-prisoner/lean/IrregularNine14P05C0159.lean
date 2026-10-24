import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0141
import IrregularNine14P05C0142
import IrregularNine14P05C0143
import IrregularNine14P05C0144
import IrregularNine14P05C0145
import IrregularNine14P05C0146
import IrregularNine14P05C0147
import IrregularNine14P05C0148
import IrregularNine14P05C0149

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9540 : PairBound 9 := { available := 445, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 11 70 445 445 445 509 445 445), lower := (rows 7 11 70 8 16 32 64 128 256), losses := [] }

theorem u9540 : Upper (D 5) (R 5) [6,9,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9540
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9541 : PairBound 9 := { available := 439, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 76 447 439 439 503 439 439), lower := (rows 7 11 76 8 16 32 64 128 256), losses := [] }

theorem u9541 : Upper (D 5) (R 5) [6,9,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9541
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9542_3 : Upper (D 5) (R 5) [6,9,80,3] 13 :=
  permutation_upper _ _ _ [6,5,9,80] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8475

theorem m9542_5 : Upper (D 5) (R 5) [6,9,80,5] 13 :=
  permutation_upper _ _ _ [6,9,10,80] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8529

theorem m9542_6 : Upper (D 5) (R 5) [6,9,80,6] 13 :=
  permutation_upper _ _ _ [6,9,9,80] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8525

theorem m9542_33 : Upper (D 5) (R 5) [6,9,80,33] 13 :=
  permutation_upper _ _ _ [6,9,34,80] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8555

theorem m9542_34 : Upper (D 5) (R 5) [6,9,80,34] 13 :=
  permutation_upper _ _ _ [6,9,33,80] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8550

theorem m9542_36 : Upper (D 5) (R 5) [6,9,80,36] 13 :=
  permutation_upper _ _ _ [6,9,40,80] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8562

theorem m9542_129 : Upper (D 5) (R 5) [6,9,80,129] 13 :=
  permutation_upper _ _ _ [6,9,66,144] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8575

theorem m9542_130 : Upper (D 5) (R 5) [6,9,80,130] 13 :=
  permutation_upper _ _ _ [6,9,65,144] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8571

theorem m9542_132 : Upper (D 5) (R 5) [6,9,80,132] 13 :=
  permutation_upper _ _ _ [6,9,72,144] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8579

def r9542 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9542 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9542 : Upper (D 5) (R 5) [6,9,80] 13 := by
  apply FastRouting.sound _ _ [6,9,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9542 c9542
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9542_3
  · exact m9542_5
  · exact m9542_6
  · exact m9542_33
  · exact m9542_34
  · exact m9542_36
  · exact m9542_129
  · exact m9542_130
  · exact m9542_132
  · exact u8582
  · exact u8583

theorem m9543_3 : Upper (D 5) (R 5) [6,9,96,3] 13 :=
  permutation_upper _ _ _ [6,5,9,96] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8476

theorem m9543_5 : Upper (D 5) (R 5) [6,9,96,5] 13 :=
  permutation_upper _ _ _ [6,9,10,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8530

theorem m9543_6 : Upper (D 5) (R 5) [6,9,96,6] 13 :=
  permutation_upper _ _ _ [6,9,9,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8526

theorem m9543_17 : Upper (D 5) (R 5) [6,9,96,17] 13 :=
  permutation_upper _ _ _ [6,9,18,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8538

theorem m9543_18 : Upper (D 5) (R 5) [6,9,96,18] 13 :=
  permutation_upper _ _ _ [6,9,17,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8534

theorem m9543_20 : Upper (D 5) (R 5) [6,9,96,20] 13 :=
  permutation_upper _ _ _ [6,9,24,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8546

theorem m9543_33 : Upper (D 5) (R 5) [6,9,96,33] 13 :=
  permutation_upper _ _ _ [6,9,34,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8556

theorem m9543_34 : Upper (D 5) (R 5) [6,9,96,34] 13 :=
  permutation_upper _ _ _ [6,9,33,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8551

theorem m9543_36 : Upper (D 5) (R 5) [6,9,96,36] 13 :=
  permutation_upper _ _ _ [6,9,40,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8563

theorem m9543_48 : Upper (D 5) (R 5) [6,9,96,48] 13 :=
  permutation_upper _ _ _ [6,9,48,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8568

theorem m9543_129 : Upper (D 5) (R 5) [6,9,96,129] 13 :=
  permutation_upper _ _ _ [6,9,66,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8576

theorem m9543_130 : Upper (D 5) (R 5) [6,9,96,130] 13 :=
  permutation_upper _ _ _ [6,9,65,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8572

theorem m9543_132 : Upper (D 5) (R 5) [6,9,96,132] 13 :=
  permutation_upper _ _ _ [6,9,72,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8580

theorem m9543_144 : Upper (D 5) (R 5) [6,9,96,144] 13 :=
  permutation_upper _ _ _ [6,9,80,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8582

def r9543 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9543 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 66 => 6 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9543 : Upper (D 5) (R 5) [6,9,96] 13 := by
  apply FastRouting.sound _ _ [6,9,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,129,130,132,144,160,384] r9543 c9543
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9543_3
  · exact m9543_5
  · exact m9543_6
  · exact m9543_17
  · exact m9543_18
  · exact m9543_20
  · exact m9543_33
  · exact m9543_34
  · exact m9543_36
  · exact m9543_48
  · exact m9543_129
  · exact m9543_130
  · exact m9543_132
  · exact m9543_144
  · exact u8584
  · exact u8585

theorem m9544_3 : Upper (D 5) (R 5) [6,9,192,3] 13 :=
  permutation_upper _ _ _ [6,5,9,192] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8477

theorem m9544_5 : Upper (D 5) (R 5) [6,9,192,5] 13 :=
  permutation_upper _ _ _ [6,9,10,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8531

theorem m9544_6 : Upper (D 5) (R 5) [6,9,192,6] 13 :=
  permutation_upper _ _ _ [6,9,9,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8527

theorem m9544_17 : Upper (D 5) (R 5) [6,9,192,17] 13 :=
  permutation_upper _ _ _ [6,9,18,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8539

theorem m9544_18 : Upper (D 5) (R 5) [6,9,192,18] 13 :=
  permutation_upper _ _ _ [6,9,17,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8535

theorem m9544_20 : Upper (D 5) (R 5) [6,9,192,20] 13 :=
  permutation_upper _ _ _ [6,9,24,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8547

theorem m9544_33 : Upper (D 5) (R 5) [6,9,192,33] 13 :=
  permutation_upper _ _ _ [6,9,34,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8557

theorem m9544_34 : Upper (D 5) (R 5) [6,9,192,34] 13 :=
  permutation_upper _ _ _ [6,9,33,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8552

theorem m9544_36 : Upper (D 5) (R 5) [6,9,192,36] 13 :=
  permutation_upper _ _ _ [6,9,40,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8564

theorem m9544_48 : Upper (D 5) (R 5) [6,9,192,48] 13 :=
  permutation_upper _ _ _ [6,9,48,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8569

theorem m9544_257 : Upper (D 5) (R 5) [6,9,192,257] 13 :=
  permutation_upper _ _ _ [6,9,66,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8577

theorem m9544_258 : Upper (D 5) (R 5) [6,9,192,258] 13 :=
  permutation_upper _ _ _ [6,9,65,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8573

theorem m9544_260 : Upper (D 5) (R 5) [6,9,192,260] 13 :=
  permutation_upper _ _ _ [6,9,72,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8581

theorem m9544_272 : Upper (D 5) (R 5) [6,9,192,272] 13 :=
  permutation_upper _ _ _ [6,9,80,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8583

theorem m9544_288 : Upper (D 5) (R 5) [6,9,192,288] 13 :=
  permutation_upper _ _ _ [6,9,96,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8585

def r9544 : Route 9 := (fun mask => (mask,id))

def c9544 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9544 : Upper (D 5) (R 5) [6,9,192] 13 := by
  apply FastRouting.sound _ _ [6,9,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r9544 c9544
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9544_3
  · exact m9544_5
  · exact m9544_6
  · exact m9544_17
  · exact m9544_18
  · exact m9544_20
  · exact m9544_33
  · exact m9544_34
  · exact m9544_36
  · exact m9544_48
  · exact m9544_257
  · exact m9544_258
  · exact m9544_260
  · exact m9544_272
  · exact m9544_288

def b9545 : PairBound 9 := { available := 491, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 21 491 507 491 491 491 491), lower := (rows 7 14 21 8 16 32 64 128 256), losses := [] }

theorem u9545 : Upper (D 5) (R 5) [6,12,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9545
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9546 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 28 491 499 483 483 483 483), lower := (rows 7 14 28 8 16 32 64 128 256), losses := [] }

theorem u9546 : Upper (D 5) (R 5) [6,12,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9546
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9547 : PairBound 9 := { available := 507, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 37 507 507 507 507 507 507), lower := (rows 7 14 37 8 16 32 64 128 256), losses := [] }

theorem u9547 : Upper (D 5) (R 5) [6,12,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9547
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9548 : PairBound 9 := { available := 499, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 44 507 499 499 499 499 499), lower := (rows 7 14 44 8 16 32 64 128 256), losses := [] }

theorem u9548 : Upper (D 5) (R 5) [6,12,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9548
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9549 : PairBound 9 := { available := 491, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 52 491 507 491 491 491 491), lower := (rows 7 14 52 8 16 32 64 128 256), losses := [] }

theorem u9549 : Upper (D 5) (R 5) [6,12,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9549
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9550 : PairBound 9 := { available := 443, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 69 443 443 443 507 443 443), lower := (rows 7 14 69 8 16 32 64 128 256), losses := [] }

theorem u9550 : Upper (D 5) (R 5) [6,12,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9550
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9551 : PairBound 9 := { available := 435, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 76 443 435 435 499 435 435), lower := (rows 7 14 76 8 16 32 64 128 256), losses := [] }

theorem u9551 : Upper (D 5) (R 5) [6,12,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9551
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9552 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 84 427 443 427 491 427 427), lower := (rows 7 14 84 8 16 32 64 128 256), losses := [] }

theorem u9552 : Upper (D 5) (R 5) [6,12,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9552
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9553 : PairBound 9 := { available := 443, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 100 443 443 443 507 443 443), lower := (rows 7 14 100 8 16 32 64 128 256), losses := [] }

theorem u9553 : Upper (D 5) (R 5) [6,12,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9553
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9554 : PairBound 9 := { available := 315, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 196 315 315 315 379 443 315), lower := (rows 7 14 196 8 16 32 64 128 256), losses := [] }

theorem u9554 : Upper (D 5) (R 5) [6,12,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9554
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9555 : PairBound 9 := { available := 494, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 37 494 510 494 494 494 494), lower := (rows 7 19 37 8 16 32 64 128 256), losses := [] }

theorem u9555 : Upper (D 5) (R 5) [6,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9555
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9556 : PairBound 9 := { available := 493, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 38 493 509 493 493 493 493), lower := (rows 7 19 38 8 16 32 64 128 256), losses := [] }

theorem u9556 : Upper (D 5) (R 5) [6,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9556
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9557_3 : Upper (D 5) (R 5) [6,17,40,3] 13 :=
  permutation_upper _ _ _ [6,12,18,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8592

theorem m9557_5 : Upper (D 5) (R 5) [6,17,40,5] 13 :=
  permutation_upper _ _ _ [6,12,33,18] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8601

def r9557 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c9557 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9557 : Upper (D 5) (R 5) [6,17,40] 13 := by
  apply FastRouting.sound _ _ [6,17,40] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,192] r9557 c9557
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9557_3
  · exact m9557_5
  · exact u8680
  · exact u8681
  · exact u8682
  · exact u8683
  · exact u8684
  · exact u8685
  · exact u8686
  · exact u8687
  · exact u8688

def b9558 : PairBound 9 := { available := 430, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 19 69 430 446 430 494 430 430), lower := (rows 7 19 69 8 16 32 64 128 256), losses := [] }

theorem u9558 : Upper (D 5) (R 5) [6,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9558
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9559 : PairBound 9 := { available := 429, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 19 70 429 445 429 493 429 429), lower := (rows 7 19 70 8 16 32 64 128 256), losses := [] }

theorem u9559 : Upper (D 5) (R 5) [6,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9559
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9560_3 : Upper (D 5) (R 5) [6,17,72,3] 13 :=
  permutation_upper _ _ _ [6,12,18,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8593

theorem m9560_5 : Upper (D 5) (R 5) [6,17,72,5] 13 :=
  permutation_upper _ _ _ [6,12,65,18] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8622

def r9560 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9560 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9560 : Upper (D 5) (R 5) [6,17,72] 13 := by
  apply FastRouting.sound _ _ [6,17,72] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9560 c9560
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9560_3
  · exact m9560_5
  · exact u8702
  · exact u8703
  · exact u8704
  · exact u8705
  · exact u8706
  · exact u8707
  · exact u8708
  · exact u8709
  · exact u8710

theorem m9561_3 : Upper (D 5) (R 5) [6,17,96,3] 13 :=
  permutation_upper _ _ _ [6,12,18,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8594

theorem m9561_5 : Upper (D 5) (R 5) [6,17,96,5] 13 :=
  permutation_upper _ _ _ [6,12,96,18] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8652

def r9561 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9561 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9561 : Upper (D 5) (R 5) [6,17,96] 13 := by
  apply FastRouting.sound _ _ [6,17,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9561 c9561
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9561_3
  · exact m9561_5
  · exact u8711
  · exact u8712
  · exact u8713
  · exact u8714
  · exact u8715
  · exact u8716
  · exact u8717
  · exact u8718
  · exact u8719

theorem m9562_3 : Upper (D 5) (R 5) [6,17,192,3] 13 :=
  permutation_upper _ _ _ [6,12,18,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8595

theorem m9562_5 : Upper (D 5) (R 5) [6,17,192,5] 13 :=
  permutation_upper _ _ _ [6,12,192,18] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8661

def r9562 : Route 9 := (fun mask => (mask,id))

def c9562 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9562 : Upper (D 5) (R 5) [6,17,192] 13 := by
  apply FastRouting.sound _ _ [6,17,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9562 c9562
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9562_3
  · exact m9562_5
  · exact u8720
  · exact u8721
  · exact u8722
  · exact u8723
  · exact u8724
  · exact u8725
  · exact u8726
  · exact u8727

def b9563 : PairBound 9 := { available := 491, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 37 491 507 491 491 491 491), lower := (rows 7 22 37 8 16 32 64 128 256), losses := [] }

theorem u9563 : Upper (D 5) (R 5) [6,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9563
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9564 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 488, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 22 38 489 505 489 489 489 489), lower := (rows 7 22 38 8 16 32 64 128 256), losses := [] }

theorem u9564 : Upper (D 5) (R 5) [6,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9564
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9565 : PairBound 9 := { available := 491, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 44 491 507 491 491 491 491), lower := (rows 7 22 44 8 16 32 64 128 256), losses := [] }

theorem u9565 : Upper (D 5) (R 5) [6,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9565
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9566 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 69 427 443 427 491 427 427), lower := (rows 7 22 69 8 16 32 64 128 256), losses := [] }

theorem u9566 : Upper (D 5) (R 5) [6,20,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9566
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9567 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 22 70 425 441 425 489 425 425), lower := (rows 7 22 70 8 16 32 64 128 256), losses := [] }

theorem u9567 : Upper (D 5) (R 5) [6,20,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9567
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9568 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 76 427 443 427 491 427 427), lower := (rows 7 22 76 8 16 32 64 128 256), losses := [] }

theorem u9568 : Upper (D 5) (R 5) [6,20,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9568
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9569 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 100 427 443 427 491 427 427), lower := (rows 7 22 100 8 16 32 64 128 256), losses := [] }

theorem u9569 : Upper (D 5) (R 5) [6,20,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9569
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9570 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 22 196 299 315 299 363 427 299), lower := (rows 7 22 196 8 16 32 64 128 256), losses := [] }

theorem u9570 : Upper (D 5) (R 5) [6,20,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9570
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9571_3 : Upper (D 5) (R 5) [6,24,33,3] 13 :=
  permutation_upper _ _ _ [6,12,17,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8587

theorem m9571_5 : Upper (D 5) (R 5) [6,24,33,5] 13 :=
  permutation_upper _ _ _ [6,12,34,17] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8608

theorem m9571_6 : Upper (D 5) (R 5) [6,24,33,6] 13 :=
  permutation_upper _ _ _ [6,17,40,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8680

def r9571 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c9571 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9571 : Upper (D 5) (R 5) [6,24,33] 13 := by
  apply FastRouting.sound _ _ [6,24,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,192] r9571 c9571
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9571_3
  · exact m9571_5
  · exact m9571_6
  · exact u8767
  · exact u8768
  · exact u8769
  · exact u8770
  · exact u8771
  · exact u8772
  · exact u8773
  · exact u8774

def b9572 : PairBound 9 := { available := 493, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 38 493 509 493 493 493 493), lower := (rows 7 26 38 8 16 32 64 128 256), losses := [] }

theorem u9572 : Upper (D 5) (R 5) [6,24,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9572
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9573_3 : Upper (D 5) (R 5) [6,24,40,3] 13 :=
  permutation_upper _ _ _ [6,12,17,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8586

theorem m9573_5 : Upper (D 5) (R 5) [6,24,40,5] 13 :=
  permutation_upper _ _ _ [6,12,33,17] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8600

theorem m9573_6 : Upper (D 5) (R 5) [6,24,40,6] 13 :=
  permutation_upper _ _ _ [6,17,33,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8669

def r9573 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c9573 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9573 : Upper (D 5) (R 5) [6,24,40] 13 := by
  apply FastRouting.sound _ _ [6,24,40] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,192] r9573 c9573
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9573_3
  · exact m9573_5
  · exact m9573_6
  · exact u8780
  · exact u8781
  · exact u8782
  · exact u8783
  · exact u8784
  · exact u8785
  · exact u8786
  · exact u8787

theorem m9574_3 : Upper (D 5) (R 5) [6,24,65,3] 13 :=
  permutation_upper _ _ _ [6,12,17,66] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8589

theorem m9574_5 : Upper (D 5) (R 5) [6,24,65,5] 13 :=
  permutation_upper _ _ _ [6,12,66,17] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8631

theorem m9574_6 : Upper (D 5) (R 5) [6,24,65,6] 13 :=
  permutation_upper _ _ _ [6,17,72,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8702

def r9574 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9574 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9574 : Upper (D 5) (R 5) [6,24,65] 13 := by
  apply FastRouting.sound _ _ [6,24,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9574 c9574
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9574_3
  · exact m9574_5
  · exact m9574_6
  · exact u8788
  · exact u8789
  · exact u8790
  · exact u8791
  · exact u8792
  · exact u8793
  · exact u8794
  · exact u8795

def b9575 : PairBound 9 := { available := 429, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 26 70 429 445 429 493 429 429), lower := (rows 7 26 70 8 16 32 64 128 256), losses := [] }

theorem u9575 : Upper (D 5) (R 5) [6,24,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9575
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9576_3 : Upper (D 5) (R 5) [6,24,72,3] 13 :=
  permutation_upper _ _ _ [6,12,17,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8588

theorem m9576_5 : Upper (D 5) (R 5) [6,24,72,5] 13 :=
  permutation_upper _ _ _ [6,12,65,17] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8621

theorem m9576_6 : Upper (D 5) (R 5) [6,24,72,6] 13 :=
  permutation_upper _ _ _ [6,17,65,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8689

def r9576 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9576 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9576 : Upper (D 5) (R 5) [6,24,72] 13 := by
  apply FastRouting.sound _ _ [6,24,72] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9576 c9576
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9576_3
  · exact m9576_5
  · exact m9576_6
  · exact u8802
  · exact u8803
  · exact u8804
  · exact u8805
  · exact u8806
  · exact u8807
  · exact u8808
  · exact u8809

theorem m9577_3 : Upper (D 5) (R 5) [6,24,96,3] 13 :=
  permutation_upper _ _ _ [6,12,17,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8590

theorem m9577_5 : Upper (D 5) (R 5) [6,24,96,5] 13 :=
  permutation_upper _ _ _ [6,12,96,17] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8651

theorem m9577_6 : Upper (D 5) (R 5) [6,24,96,6] 13 :=
  permutation_upper _ _ _ [6,17,96,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8711

def r9577 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9577 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9577 : Upper (D 5) (R 5) [6,24,96] 13 := by
  apply FastRouting.sound _ _ [6,24,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9577 c9577
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9577_3
  · exact m9577_5
  · exact m9577_6
  · exact u8810
  · exact u8811
  · exact u8812
  · exact u8813
  · exact u8814
  · exact u8815
  · exact u8816
  · exact u8817

theorem m9578_3 : Upper (D 5) (R 5) [6,24,192,3] 13 :=
  permutation_upper _ _ _ [6,12,17,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8591

theorem m9578_5 : Upper (D 5) (R 5) [6,24,192,5] 13 :=
  permutation_upper _ _ _ [6,12,192,17] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8660

theorem m9578_6 : Upper (D 5) (R 5) [6,24,192,6] 13 :=
  permutation_upper _ _ _ [6,17,192,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8720

def r9578 : Route 9 := (fun mask => (mask,id))

def c9578 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9578 : Upper (D 5) (R 5) [6,24,192] 13 := by
  apply FastRouting.sound _ _ [6,24,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9578 c9578
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9578_3
  · exact m9578_5
  · exact m9578_6
  · exact u8818
  · exact u8819
  · exact u8820
  · exact u8821
  · exact u8822
  · exact u8823
  · exact u8824

def b9579 : PairBound 9 := { available := 478, camps := [{ cop := 5, region := 7, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 37 478 478 510 478 478 478), lower := (rows 7 35 37 8 16 32 64 128 256), losses := [] }

theorem u9579 : Upper (D 5) (R 5) [6,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9579
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9580 : PairBound 9 := { available := 477, camps := [{ cop := 2, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 35 38 477 477 509 477 477 477), lower := (rows 7 35 38 8 16 32 64 128 256), losses := [] }

theorem u9580 : Upper (D 5) (R 5) [6,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9580
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9581 : PairBound 9 := { available := 479, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 44 479 479 511 479 479 479), lower := (rows 7 35 44 8 16 32 64 128 256), losses := [] }

theorem u9581 : Upper (D 5) (R 5) [6,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9581
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9582 : PairBound 9 := { available := 463, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 52 463 479 495 463 463 463), lower := (rows 7 35 52 8 16 32 64 128 256), losses := [] }

theorem u9582 : Upper (D 5) (R 5) [6,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9582
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9583 : PairBound 9 := { available := 446, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 446 446 446 510 446 446), lower := (rows 7 35 69 8 16 32 64 128 256), losses := [] }

theorem u9583 : Upper (D 5) (R 5) [6,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9583
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9584 : PairBound 9 := { available := 445, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 70 445 445 445 509 445 445), lower := (rows 7 35 70 8 16 32 64 128 256), losses := [] }

theorem u9584 : Upper (D 5) (R 5) [6,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9584
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9585_3 : Upper (D 5) (R 5) [6,33,72,3] 13 :=
  permutation_upper _ _ _ [6,12,34,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8609

theorem m9585_5 : Upper (D 5) (R 5) [6,33,72,5] 13 :=
  permutation_upper _ _ _ [6,12,65,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8624

def r9585 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9585 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 66 => 6 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9585 : Upper (D 5) (R 5) [6,33,72] 13 := by
  apply FastRouting.sound _ _ [6,33,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,129,130,132,144,160,384] r9585 c9585
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9585_3
  · exact m9585_5
  · exact u8864
  · exact u8865
  · exact u8866
  · exact u8867
  · exact u8868
  · exact u8869
  · exact u8870
  · exact u8871
  · exact u8872
  · exact u8873
  · exact u8874
  · exact u8875
  · exact u8876
  · exact u8877

theorem m9586_3 : Upper (D 5) (R 5) [6,33,80,3] 13 :=
  permutation_upper _ _ _ [6,12,34,80] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8610

theorem m9586_5 : Upper (D 5) (R 5) [6,33,80,5] 13 :=
  permutation_upper _ _ _ [6,12,80,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8646

def r9586 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9586 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9586 : Upper (D 5) (R 5) [6,33,80] 13 := by
  apply FastRouting.sound _ _ [6,33,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9586 c9586
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9586_3
  · exact m9586_5
  · exact u8878
  · exact u8879
  · exact u8880
  · exact u8881
  · exact u8882
  · exact u8883
  · exact u8884
  · exact u8885
  · exact u8886

def b9587 : PairBound 9 := { available := 415, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 100 415 415 447 479 415 415), lower := (rows 7 35 100 8 16 32 64 128 256), losses := [] }

theorem u9587 : Upper (D 5) (R 5) [6,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9587
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9588_3 : Upper (D 5) (R 5) [6,33,192,3] 13 :=
  permutation_upper _ _ _ [6,12,34,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8611

theorem m9588_5 : Upper (D 5) (R 5) [6,33,192,5] 13 :=
  permutation_upper _ _ _ [6,12,192,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8663

def r9588 : Route 9 := (fun mask => (mask,id))

def c9588 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9588 : Upper (D 5) (R 5) [6,33,192] 13 := by
  apply FastRouting.sound _ _ [6,33,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r9588 c9588
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9588_3
  · exact m9588_5
  · exact u8895
  · exact u8896
  · exact u8897
  · exact u8898
  · exact u8899
  · exact u8900
  · exact u8901
  · exact u8902
  · exact u8903
  · exact u8904
  · exact u8905
  · exact u8906
  · exact u8907

def b9589 : PairBound 9 := { available := 475, camps := [{ cop := 1, region := 473, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 44 475 475 507 475 475 475), lower := (rows 7 38 44 8 16 32 64 128 256), losses := [] }

theorem u9589 : Upper (D 5) (R 5) [6,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9589
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9590 : PairBound 9 := { available := 459, camps := [{ cop := 1, region := 457, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 52 459 475 491 459 459 459), lower := (rows 7 38 52 8 16 32 64 128 256), losses := [] }

theorem u9590 : Upper (D 5) (R 5) [6,36,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9590
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9591 : PairBound 9 := { available := 443, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 69 443 443 443 507 443 443), lower := (rows 7 38 69 8 16 32 64 128 256), losses := [] }

theorem u9591 : Upper (D 5) (R 5) [6,36,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9591
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9592 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 38 70 441 441 441 505 441 441), lower := (rows 7 38 70 8 16 32 64 128 256), losses := [] }

theorem u9592 : Upper (D 5) (R 5) [6,36,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9592
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9593 : PairBound 9 := { available := 443, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 76 443 443 443 507 443 443), lower := (rows 7 38 76 8 16 32 64 128 256), losses := [] }

theorem u9593 : Upper (D 5) (R 5) [6,36,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9593
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9594 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 84 427 443 427 491 427 427), lower := (rows 7 38 84 8 16 32 64 128 256), losses := [] }

theorem u9594 : Upper (D 5) (R 5) [6,36,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9594
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9595 : PairBound 9 := { available := 411, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 7 38 100 411 411 443 475 411 411), lower := (rows 7 38 100 8 16 32 64 128 256), losses := [] }

theorem u9595 : Upper (D 5) (R 5) [6,36,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9595
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9596 : PairBound 9 := { available := 315, camps := [{ cop := 0, region := 312, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 38 196 315 315 315 379 443 315), lower := (rows 7 38 196 8 16 32 64 128 256), losses := [] }

theorem u9596 : Upper (D 5) (R 5) [6,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9596
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9597 : PairBound 9 := { available := 471, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 44 479 471 503 471 471 471), lower := (rows 7 42 44 8 16 32 64 128 256), losses := [] }

theorem u9597 : Upper (D 5) (R 5) [6,40,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9597
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9598 : PairBound 9 := { available := 463, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 42 52 463 479 495 463 463 463), lower := (rows 7 42 52 8 16 32 64 128 256), losses := [] }

theorem u9598 : Upper (D 5) (R 5) [6,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9598
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9599_3 : Upper (D 5) (R 5) [6,40,65,3] 13 :=
  permutation_upper _ _ _ [6,12,33,66] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8604

theorem m9599_5 : Upper (D 5) (R 5) [6,40,65,5] 13 :=
  permutation_upper _ _ _ [6,12,66,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8632

theorem m9599_6 : Upper (D 5) (R 5) [6,40,65,6] 13 :=
  permutation_upper _ _ _ [6,33,72,6] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8864

def r9599 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9599 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 66 => 6 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9599 : Upper (D 5) (R 5) [6,40,65] 13 := by
  apply FastRouting.sound _ _ [6,40,65] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,129,130,132,144,160,384] r9599 c9599
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9599_3
  · exact m9599_5
  · exact m9599_6
  · exact u8966
  · exact u8967
  · exact u8968
  · exact u8969
  · exact u8970
  · exact u8971
  · exact u8972
  · exact u8973
  · exact u8974
  · exact u8975
  · exact u8976
  · exact u8977
  · exact u8978

#print axioms u9599
end Delivery.IrregularNine14.P05
