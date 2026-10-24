import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P04C0008
import IrregularNine14P04C0009
import IrregularNine14P04C0010
import IrregularNine14P04C0011
import IrregularNine14P04C0012

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m780_3 : Upper (D 4) (R 4) [6,96,384,3] 13 :=
  permutation_upper _ _ _ [6,12,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u575

theorem m780_5 : Upper (D 4) (R 4) [6,96,384,5] 13 :=
  permutation_upper _ _ _ [6,12,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u575

theorem m780_20 : Upper (D 4) (R 4) [6,96,384,20] 13 :=
  permutation_upper _ _ _ [6,96,384,18] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u695

def r780 : Route 9 := (fun mask => (mask,id))

def c780 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 5 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u780 : Upper (D 4) (R 4) [6,96,384] 13 := by
  apply FastRouting.sound _ _ [6,96,384] 13 (by decide) (choices 2) [3,5,6,17,18,20] r780 c780
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m780_3
  · exact m780_5
  · exact u693
  · exact u694
  · exact u695
  · exact m780_20

def b781 : PairBound 9 := { available := 470, camps := [{ cop := 3, region := 3, targets := 4 }], pairs := [(0,2)], upper := (rows 11 11 37 478 470 502 470 470 470), lower := (rows 11 11 37 8 16 32 64 128 256), losses := [] }

theorem u781 : Upper (D 4) (R 4) [10,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b781
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b782 : PairBound 9 := { available := 407, camps := [{ cop := 3, region := 3, targets := 4 }], pairs := [(0,2)], upper := (rows 11 11 100 415 407 439 471 407 407), lower := (rows 11 11 100 8 16 32 64 128 256), losses := [] }

theorem u782 : Upper (D 4) (R 4) [10,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b782
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b783 : PairBound 9 := { available := 471, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3)], upper := (rows 11 14 37 479 471 503 471 471 471), lower := (rows 11 14 37 8 16 32 64 128 256), losses := [] }

theorem u783 : Upper (D 4) (R 4) [10,12,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b783
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b784 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3)], upper := (rows 11 14 100 415 407 439 471 407 407), lower := (rows 11 14 100 8 16 32 64 128 256), losses := [] }

theorem u784 : Upper (D 4) (R 4) [10,12,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b784
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m785_6 : Upper (D 4) (R 4) [10,17,33,6] 13 :=
  permutation_upper _ _ _ [6,12,17,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u556

theorem m785_18 : Upper (D 4) (R 4) [10,17,33,18] 13 :=
  permutation_upper _ _ _ [6,17,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u577

theorem m785_20 : Upper (D 4) (R 4) [10,17,33,20] 13 :=
  permutation_upper _ _ _ [6,17,24,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u579

theorem m785_66 : Upper (D 4) (R 4) [10,17,33,66] 13 :=
  permutation_upper _ _ _ [6,17,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u583

theorem m785_68 : Upper (D 4) (R 4) [10,17,33,68] 13 :=
  permutation_upper _ _ _ [6,17,40,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u587

theorem m785_80 : Upper (D 4) (R 4) [10,17,33,80] 13 :=
  permutation_upper _ _ _ [6,17,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u591

theorem m785_192 : Upper (D 4) (R 4) [10,17,33,192] 13 :=
  permutation_upper _ _ _ [6,17,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u594

def r785 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c785 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u785 : Upper (D 4) (R 4) [10,17,33] 13 := by
  apply FastRouting.sound _ _ [10,17,33] 13 (by decide) (choices 2) [6,18,20,66,68,80,192] r785 c785
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m785_6
  · exact m785_18
  · exact m785_20
  · exact m785_66
  · exact m785_68
  · exact m785_80
  · exact m785_192

theorem m786_3 : Upper (D 4) (R 4) [10,17,96,3] 13 :=
  permutation_upper _ _ _ [6,5,17,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u523

theorem m786_5 : Upper (D 4) (R 4) [10,17,96,5] 13 :=
  permutation_upper _ _ _ [6,9,17,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u538

theorem m786_6 : Upper (D 4) (R 4) [10,17,96,6] 13 :=
  permutation_upper _ _ _ [6,12,17,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u558

theorem m786_17 : Upper (D 4) (R 4) [10,17,96,17] 13 :=
  permutation_upper _ _ _ [6,17,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u576

theorem m786_18 : Upper (D 4) (R 4) [10,17,96,18] 13 :=
  permutation_upper _ _ _ [6,17,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u578

theorem m786_20 : Upper (D 4) (R 4) [10,17,96,20] 13 :=
  permutation_upper _ _ _ [6,17,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u580

theorem m786_129 : Upper (D 4) (R 4) [10,17,96,129] 13 :=
  permutation_upper _ _ _ [6,17,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u582

theorem m786_130 : Upper (D 4) (R 4) [10,17,96,130] 13 :=
  permutation_upper _ _ _ [6,17,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u585

theorem m786_132 : Upper (D 4) (R 4) [10,17,96,132] 13 :=
  permutation_upper _ _ _ [6,17,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u590

theorem m786_144 : Upper (D 4) (R 4) [10,17,96,144] 13 :=
  permutation_upper _ _ _ [6,17,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u592

theorem m786_384 : Upper (D 4) (R 4) [10,17,96,384] 13 :=
  permutation_upper _ _ _ [6,17,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u597

def r786 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c786 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u786 : Upper (D 4) (R 4) [10,17,96] 13 := by
  apply FastRouting.sound _ _ [10,17,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r786 c786
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m786_3
  · exact m786_5
  · exact m786_6
  · exact m786_17
  · exact m786_18
  · exact m786_20
  · exact m786_129
  · exact m786_130
  · exact m786_132
  · exact m786_144
  · exact m786_384

theorem m787_3 : Upper (D 4) (R 4) [10,20,33,3] 13 :=
  permutation_upper _ _ _ [6,5,24,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u524

theorem m787_5 : Upper (D 4) (R 4) [10,20,33,5] 13 :=
  permutation_upper _ _ _ [6,9,24,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u541

theorem m787_6 : Upper (D 4) (R 4) [10,20,33,6] 13 :=
  permutation_upper _ _ _ [6,12,24,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u559

theorem m787_17 : Upper (D 4) (R 4) [10,20,33,17] 13 :=
  permutation_upper _ _ _ [6,17,24,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u579

theorem m787_18 : Upper (D 4) (R 4) [10,20,33,18] 13 :=
  permutation_upper _ _ _ [6,20,24,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u598

theorem m787_20 : Upper (D 4) (R 4) [10,20,33,20] 13 :=
  permutation_upper _ _ _ [6,24,24,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u608

theorem m787_65 : Upper (D 4) (R 4) [10,20,33,65] 13 :=
  permutation_upper _ _ _ [6,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u613

theorem m787_66 : Upper (D 4) (R 4) [10,20,33,66] 13 :=
  permutation_upper _ _ _ [6,24,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u618

theorem m787_68 : Upper (D 4) (R 4) [10,20,33,68] 13 :=
  permutation_upper _ _ _ [6,24,40,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u620

theorem m787_80 : Upper (D 4) (R 4) [10,20,33,80] 13 :=
  permutation_upper _ _ _ [6,24,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u623

theorem m787_192 : Upper (D 4) (R 4) [10,20,33,192] 13 :=
  permutation_upper _ _ _ [6,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u628

def r787 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c787 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u787 : Upper (D 4) (R 4) [10,20,33] 13 := by
  apply FastRouting.sound _ _ [10,20,33] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,192] r787 c787
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m787_3
  · exact m787_5
  · exact m787_6
  · exact m787_17
  · exact m787_18
  · exact m787_20
  · exact m787_65
  · exact m787_66
  · exact m787_68
  · exact m787_80
  · exact m787_192

theorem m788_3 : Upper (D 4) (R 4) [10,20,96,3] 13 :=
  permutation_upper _ _ _ [6,5,24,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u525

theorem m788_5 : Upper (D 4) (R 4) [10,20,96,5] 13 :=
  permutation_upper _ _ _ [6,9,24,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u543

theorem m788_6 : Upper (D 4) (R 4) [10,20,96,6] 13 :=
  permutation_upper _ _ _ [6,12,24,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u560

theorem m788_17 : Upper (D 4) (R 4) [10,20,96,17] 13 :=
  permutation_upper _ _ _ [6,17,24,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u580

theorem m788_18 : Upper (D 4) (R 4) [10,20,96,18] 13 :=
  permutation_upper _ _ _ [6,20,24,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u599

theorem m788_20 : Upper (D 4) (R 4) [10,20,96,20] 13 :=
  permutation_upper _ _ _ [6,24,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u609

theorem m788_129 : Upper (D 4) (R 4) [10,20,96,129] 13 :=
  permutation_upper _ _ _ [6,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u617

theorem m788_130 : Upper (D 4) (R 4) [10,20,96,130] 13 :=
  permutation_upper _ _ _ [6,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u619

theorem m788_132 : Upper (D 4) (R 4) [10,20,96,132] 13 :=
  permutation_upper _ _ _ [6,24,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u622

theorem m788_144 : Upper (D 4) (R 4) [10,20,96,144] 13 :=
  permutation_upper _ _ _ [6,24,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u624

theorem m788_384 : Upper (D 4) (R 4) [10,20,96,384] 13 :=
  permutation_upper _ _ _ [6,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u632

def r788 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c788 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u788 : Upper (D 4) (R 4) [10,20,96] 13 := by
  apply FastRouting.sound _ _ [10,20,96] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r788 c788
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m788_3
  · exact m788_5
  · exact m788_6
  · exact m788_17
  · exact m788_18
  · exact m788_20
  · exact m788_129
  · exact m788_130
  · exact m788_132
  · exact m788_144
  · exact m788_384

def b789 : PairBound 9 := { available := 471, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3)], upper := (rows 11 26 37 479 471 503 471 471 471), lower := (rows 11 26 37 8 16 32 64 128 256), losses := [] }

theorem u789 : Upper (D 4) (R 4) [10,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b789
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b790 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 500, targets := 8 }], pairs := [(2,3)], upper := (rows 11 26 100 415 407 439 471 407 407), lower := (rows 11 26 100 8 16 32 64 128 256), losses := [] }

theorem u790 : Upper (D 4) (R 4) [10,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b790
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m791_6 : Upper (D 4) (R 4) [10,33,65,6] 13 :=
  permutation_upper _ _ _ [6,12,33,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u561

theorem m791_18 : Upper (D 4) (R 4) [10,33,65,18] 13 :=
  permutation_upper _ _ _ [6,20,33,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u600

theorem m791_20 : Upper (D 4) (R 4) [10,33,65,20] 13 :=
  permutation_upper _ _ _ [6,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u613

theorem m791_130 : Upper (D 4) (R 4) [10,33,65,130] 13 :=
  permutation_upper _ _ _ [6,33,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u635

theorem m791_132 : Upper (D 4) (R 4) [10,33,65,132] 13 :=
  permutation_upper _ _ _ [6,33,72,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u642

theorem m791_144 : Upper (D 4) (R 4) [10,33,65,144] 13 :=
  permutation_upper _ _ _ [6,33,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u648

theorem m791_384 : Upper (D 4) (R 4) [10,33,65,384] 13 :=
  permutation_upper _ _ _ [6,33,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u655

def r791 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c791 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u791 : Upper (D 4) (R 4) [10,33,65] 13 := by
  apply FastRouting.sound _ _ [10,33,65] 13 (by decide) (choices 2) [6,18,20,130,132,144,384] r791 c791
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m791_6
  · exact m791_18
  · exact m791_20
  · exact m791_130
  · exact m791_132
  · exact m791_144
  · exact m791_384

theorem m792_5 : Upper (D 4) (R 4) [10,33,66,5] 13 :=
  permutation_upper _ _ _ [6,9,33,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u544

theorem m792_17 : Upper (D 4) (R 4) [10,33,66,17] 13 :=
  permutation_upper _ _ _ [6,17,33,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u581

theorem m792_20 : Upper (D 4) (R 4) [10,33,66,20] 13 :=
  permutation_upper _ _ _ [6,24,33,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u615

theorem m792_129 : Upper (D 4) (R 4) [10,33,66,129] 13 :=
  permutation_upper _ _ _ [6,33,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u633

theorem m792_132 : Upper (D 4) (R 4) [10,33,66,132] 13 :=
  permutation_upper _ _ _ [6,33,72,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u643

theorem m792_144 : Upper (D 4) (R 4) [10,33,66,144] 13 :=
  permutation_upper _ _ _ [6,33,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u649

theorem m792_384 : Upper (D 4) (R 4) [10,33,66,384] 13 :=
  permutation_upper _ _ _ [6,33,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u656

def r792 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c792 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u792 : Upper (D 4) (R 4) [10,33,66] 13 := by
  apply FastRouting.sound _ _ [10,33,66] 13 (by decide) (choices 2) [5,17,20,129,132,144,384] r792 c792
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m792_5
  · exact m792_17
  · exact m792_20
  · exact m792_129
  · exact m792_132
  · exact m792_144
  · exact m792_384

theorem m793_3 : Upper (D 4) (R 4) [10,33,192,3] 13 :=
  permutation_upper _ _ _ [6,5,33,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u526

theorem m793_5 : Upper (D 4) (R 4) [10,33,192,5] 13 :=
  permutation_upper _ _ _ [6,9,33,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u546

theorem m793_6 : Upper (D 4) (R 4) [10,33,192,6] 13 :=
  permutation_upper _ _ _ [6,12,33,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u564

theorem m793_17 : Upper (D 4) (R 4) [10,33,192,17] 13 :=
  permutation_upper _ _ _ [6,17,33,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u582

theorem m793_18 : Upper (D 4) (R 4) [10,33,192,18] 13 :=
  permutation_upper _ _ _ [6,20,33,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u601

theorem m793_20 : Upper (D 4) (R 4) [10,33,192,20] 13 :=
  permutation_upper _ _ _ [6,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u617

theorem m793_257 : Upper (D 4) (R 4) [10,33,192,257] 13 :=
  permutation_upper _ _ _ [6,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u634

theorem m793_258 : Upper (D 4) (R 4) [10,33,192,258] 13 :=
  permutation_upper _ _ _ [6,33,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u637

theorem m793_260 : Upper (D 4) (R 4) [10,33,192,260] 13 :=
  permutation_upper _ _ _ [6,33,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u646

theorem m793_272 : Upper (D 4) (R 4) [10,33,192,272] 13 :=
  permutation_upper _ _ _ [6,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u650

def r793 : Route 9 := (fun mask => (mask,id))

def c793 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u793 : Upper (D 4) (R 4) [10,33,192] 13 := by
  apply FastRouting.sound _ _ [10,33,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r793 c793
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m793_3
  · exact m793_5
  · exact m793_6
  · exact m793_17
  · exact m793_18
  · exact m793_20
  · exact m793_257
  · exact m793_258
  · exact m793_260
  · exact m793_272

theorem m794_3 : Upper (D 4) (R 4) [10,36,65,3] 13 :=
  permutation_upper _ _ _ [6,5,40,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u527

theorem m794_5 : Upper (D 4) (R 4) [10,36,65,5] 13 :=
  permutation_upper _ _ _ [6,9,34,68] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u547

theorem m794_6 : Upper (D 4) (R 4) [10,36,65,6] 13 :=
  permutation_upper _ _ _ [6,12,40,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u568

theorem m794_17 : Upper (D 4) (R 4) [10,36,65,17] 13 :=
  permutation_upper _ _ _ [6,17,40,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u587

theorem m794_18 : Upper (D 4) (R 4) [10,36,65,18] 13 :=
  permutation_upper _ _ _ [6,20,40,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u602

theorem m794_20 : Upper (D 4) (R 4) [10,36,65,20] 13 :=
  permutation_upper _ _ _ [6,24,40,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u620

theorem m794_129 : Upper (D 4) (R 4) [10,36,65,129] 13 :=
  permutation_upper _ _ _ [6,33,72,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u642

theorem m794_130 : Upper (D 4) (R 4) [10,36,65,130] 13 :=
  permutation_upper _ _ _ [6,36,72,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u663

theorem m794_132 : Upper (D 4) (R 4) [10,36,65,132] 13 :=
  permutation_upper _ _ _ [6,40,72,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u671

theorem m794_144 : Upper (D 4) (R 4) [10,36,65,144] 13 :=
  permutation_upper _ _ _ [6,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u677

theorem m794_384 : Upper (D 4) (R 4) [10,36,65,384] 13 :=
  permutation_upper _ _ _ [6,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u685

def r794 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c794 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u794 : Upper (D 4) (R 4) [10,36,65] 13 := by
  apply FastRouting.sound _ _ [10,36,65] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r794 c794
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m794_3
  · exact m794_5
  · exact m794_6
  · exact m794_17
  · exact m794_18
  · exact m794_20
  · exact m794_129
  · exact m794_130
  · exact m794_132
  · exact m794_144
  · exact m794_384

theorem m795_5 : Upper (D 4) (R 4) [10,36,66,5] 13 :=
  permutation_upper _ _ _ [6,9,40,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u550

theorem m795_17 : Upper (D 4) (R 4) [10,36,66,17] 13 :=
  permutation_upper _ _ _ [6,17,40,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u589

theorem m795_20 : Upper (D 4) (R 4) [10,36,66,20] 13 :=
  permutation_upper _ _ _ [6,24,40,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u621

theorem m795_129 : Upper (D 4) (R 4) [10,36,66,129] 13 :=
  permutation_upper _ _ _ [6,33,72,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u644

theorem m795_132 : Upper (D 4) (R 4) [10,36,66,132] 13 :=
  permutation_upper _ _ _ [6,40,72,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u672

theorem m795_144 : Upper (D 4) (R 4) [10,36,66,144] 13 :=
  permutation_upper _ _ _ [6,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u678

theorem m795_384 : Upper (D 4) (R 4) [10,36,66,384] 13 :=
  permutation_upper _ _ _ [6,40,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u686

def r795 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c795 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u795 : Upper (D 4) (R 4) [10,36,66] 13 := by
  apply FastRouting.sound _ _ [10,36,66] 13 (by decide) (choices 2) [5,17,20,129,132,144,384] r795 c795
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m795_5
  · exact m795_17
  · exact m795_20
  · exact m795_129
  · exact m795_132
  · exact m795_144
  · exact m795_384

theorem m796_3 : Upper (D 4) (R 4) [10,36,192,3] 13 :=
  permutation_upper _ _ _ [6,5,40,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u528

theorem m796_5 : Upper (D 4) (R 4) [10,36,192,5] 13 :=
  permutation_upper _ _ _ [6,9,40,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u552

theorem m796_6 : Upper (D 4) (R 4) [10,36,192,6] 13 :=
  permutation_upper _ _ _ [6,12,40,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u569

theorem m796_17 : Upper (D 4) (R 4) [10,36,192,17] 13 :=
  permutation_upper _ _ _ [6,17,40,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u590

theorem m796_18 : Upper (D 4) (R 4) [10,36,192,18] 13 :=
  permutation_upper _ _ _ [6,20,40,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u603

theorem m796_20 : Upper (D 4) (R 4) [10,36,192,20] 13 :=
  permutation_upper _ _ _ [6,24,40,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u622

theorem m796_257 : Upper (D 4) (R 4) [10,36,192,257] 13 :=
  permutation_upper _ _ _ [6,33,72,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u646

theorem m796_258 : Upper (D 4) (R 4) [10,36,192,258] 13 :=
  permutation_upper _ _ _ [6,36,72,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u665

theorem m796_260 : Upper (D 4) (R 4) [10,36,192,260] 13 :=
  permutation_upper _ _ _ [6,40,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u673

theorem m796_272 : Upper (D 4) (R 4) [10,36,192,272] 13 :=
  permutation_upper _ _ _ [6,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u681

def r796 : Route 9 := (fun mask => (mask,id))

def c796 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u796 : Upper (D 4) (R 4) [10,36,192] 13 := by
  apply FastRouting.sound _ _ [10,36,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r796 c796
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m796_3
  · exact m796_5
  · exact m796_6
  · exact m796_17
  · exact m796_18
  · exact m796_20
  · exact m796_257
  · exact m796_258
  · exact m796_260
  · exact m796_272

def b797 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 468, targets := 8 }], pairs := [(2,3)], upper := (rows 11 42 69 415 407 439 471 407 407), lower := (rows 11 42 69 8 16 32 64 128 256), losses := [] }

theorem u797 : Upper (D 4) (R 4) [10,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b797
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b798 : PairBound 9 := { available := 279, camps := [{ cop := 0, region := 468, targets := 8 }], pairs := [(2,3)], upper := (rows 11 42 196 287 279 311 343 407 279), lower := (rows 11 42 196 8 16 32 64 128 256), losses := [] }

theorem u798 : Upper (D 4) (R 4) [10,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b798
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m799_3 : Upper (D 4) (R 4) [10,48,65,3] 13 :=
  permutation_upper _ _ _ [6,5,48,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u529

theorem m799_5 : Upper (D 4) (R 4) [10,48,65,5] 13 :=
  permutation_upper _ _ _ [6,9,34,80] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u548

theorem m799_6 : Upper (D 4) (R 4) [10,48,65,6] 13 :=
  permutation_upper _ _ _ [6,12,48,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u570

theorem m799_17 : Upper (D 4) (R 4) [10,48,65,17] 13 :=
  permutation_upper _ _ _ [6,17,48,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u591

theorem m799_18 : Upper (D 4) (R 4) [10,48,65,18] 13 :=
  permutation_upper _ _ _ [6,20,48,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u604

theorem m799_20 : Upper (D 4) (R 4) [10,48,65,20] 13 :=
  permutation_upper _ _ _ [6,24,48,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u623

theorem m799_129 : Upper (D 4) (R 4) [10,48,65,129] 13 :=
  permutation_upper _ _ _ [6,33,80,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u648

theorem m799_130 : Upper (D 4) (R 4) [10,48,65,130] 13 :=
  permutation_upper _ _ _ [6,36,80,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u666

theorem m799_132 : Upper (D 4) (R 4) [10,48,65,132] 13 :=
  permutation_upper _ _ _ [6,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u677

theorem m799_144 : Upper (D 4) (R 4) [10,48,65,144] 13 :=
  permutation_upper _ _ _ [6,48,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u689

theorem m799_384 : Upper (D 4) (R 4) [10,48,65,384] 13 :=
  permutation_upper _ _ _ [6,48,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u691

def r799 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c799 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u799 : Upper (D 4) (R 4) [10,48,65] 13 := by
  apply FastRouting.sound _ _ [10,48,65] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r799 c799
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m799_3
  · exact m799_5
  · exact m799_6
  · exact m799_17
  · exact m799_18
  · exact m799_20
  · exact m799_129
  · exact m799_130
  · exact m799_132
  · exact m799_144
  · exact m799_384

theorem m800_3 : Upper (D 4) (R 4) [10,48,192,3] 13 :=
  permutation_upper _ _ _ [6,5,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u530

theorem m800_5 : Upper (D 4) (R 4) [10,48,192,5] 13 :=
  permutation_upper _ _ _ [6,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u554

theorem m800_6 : Upper (D 4) (R 4) [10,48,192,6] 13 :=
  permutation_upper _ _ _ [6,12,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u571

theorem m800_17 : Upper (D 4) (R 4) [10,48,192,17] 13 :=
  permutation_upper _ _ _ [6,17,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u592

theorem m800_18 : Upper (D 4) (R 4) [10,48,192,18] 13 :=
  permutation_upper _ _ _ [6,20,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u605

theorem m800_20 : Upper (D 4) (R 4) [10,48,192,20] 13 :=
  permutation_upper _ _ _ [6,24,48,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u624

theorem m800_257 : Upper (D 4) (R 4) [10,48,192,257] 13 :=
  permutation_upper _ _ _ [6,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u650

theorem m800_258 : Upper (D 4) (R 4) [10,48,192,258] 13 :=
  permutation_upper _ _ _ [6,36,80,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u667

theorem m800_260 : Upper (D 4) (R 4) [10,48,192,260] 13 :=
  permutation_upper _ _ _ [6,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u681

theorem m800_272 : Upper (D 4) (R 4) [10,48,192,272] 13 :=
  permutation_upper _ _ _ [6,48,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u690

def r800 : Route 9 := (fun mask => (mask,id))

def c800 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u800 : Upper (D 4) (R 4) [10,48,192] 13 := by
  apply FastRouting.sound _ _ [10,48,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r800 c800
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m800_3
  · exact m800_5
  · exact m800_6
  · exact m800_17
  · exact m800_18
  · exact m800_20
  · exact m800_257
  · exact m800_258
  · exact m800_260
  · exact m800_272

theorem m801_3 : Upper (D 4) (R 4) [10,96,129,3] 13 :=
  permutation_upper _ _ _ [6,5,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u531

theorem m801_5 : Upper (D 4) (R 4) [10,96,129,5] 13 :=
  permutation_upper _ _ _ [6,9,34,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u549

theorem m801_6 : Upper (D 4) (R 4) [10,96,129,6] 13 :=
  permutation_upper _ _ _ [6,12,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u573

theorem m801_17 : Upper (D 4) (R 4) [10,96,129,17] 13 :=
  permutation_upper _ _ _ [6,17,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u594

theorem m801_18 : Upper (D 4) (R 4) [10,96,129,18] 13 :=
  permutation_upper _ _ _ [6,20,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u606

theorem m801_20 : Upper (D 4) (R 4) [10,96,129,20] 13 :=
  permutation_upper _ _ _ [6,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u628

theorem m801_257 : Upper (D 4) (R 4) [10,96,129,257] 13 :=
  permutation_upper _ _ _ [6,33,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u655

theorem m801_258 : Upper (D 4) (R 4) [10,96,129,258] 13 :=
  permutation_upper _ _ _ [6,36,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u669

theorem m801_260 : Upper (D 4) (R 4) [10,96,129,260] 13 :=
  permutation_upper _ _ _ [6,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u685

theorem m801_272 : Upper (D 4) (R 4) [10,96,129,272] 13 :=
  permutation_upper _ _ _ [6,48,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u691

def r801 : Route 9 := (fun mask => (mask,id))

def c801 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u801 : Upper (D 4) (R 4) [10,96,129] 13 := by
  apply FastRouting.sound _ _ [10,96,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r801 c801
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m801_3
  · exact m801_5
  · exact m801_6
  · exact m801_17
  · exact m801_18
  · exact m801_20
  · exact m801_257
  · exact m801_258
  · exact m801_260
  · exact m801_272

theorem m802_5 : Upper (D 4) (R 4) [10,96,130,5] 13 :=
  permutation_upper _ _ _ [6,9,40,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u552

theorem m802_17 : Upper (D 4) (R 4) [10,96,130,17] 13 :=
  permutation_upper _ _ _ [6,17,96,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u596

theorem m802_20 : Upper (D 4) (R 4) [10,96,130,20] 13 :=
  permutation_upper _ _ _ [6,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u630

theorem m802_257 : Upper (D 4) (R 4) [10,96,130,257] 13 :=
  permutation_upper _ _ _ [6,33,192,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u657

theorem m802_260 : Upper (D 4) (R 4) [10,96,130,260] 13 :=
  permutation_upper _ _ _ [6,40,192,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u687

theorem m802_272 : Upper (D 4) (R 4) [10,96,130,272] 13 :=
  permutation_upper _ _ _ [6,48,192,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u692

def r802 : Route 9 := (fun mask => (mask,id))

def c802 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u802 : Upper (D 4) (R 4) [10,96,130] 13 := by
  apply FastRouting.sound _ _ [10,96,130] 13 (by decide) (choices 2) [5,17,20,257,260,272] r802 c802
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m802_5
  · exact m802_17
  · exact m802_20
  · exact m802_257
  · exact m802_260
  · exact m802_272

theorem m803_3 : Upper (D 4) (R 4) [10,96,384,3] 13 :=
  permutation_upper _ _ _ [6,5,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u532

theorem m803_5 : Upper (D 4) (R 4) [10,96,384,5] 13 :=
  permutation_upper _ _ _ [6,9,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u555

theorem m803_6 : Upper (D 4) (R 4) [10,96,384,6] 13 :=
  permutation_upper _ _ _ [6,12,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u575

theorem m803_17 : Upper (D 4) (R 4) [10,96,384,17] 13 :=
  permutation_upper _ _ _ [6,17,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u597

theorem m803_18 : Upper (D 4) (R 4) [10,96,384,18] 13 :=
  permutation_upper _ _ _ [6,20,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u607

theorem m803_20 : Upper (D 4) (R 4) [10,96,384,20] 13 :=
  permutation_upper _ _ _ [6,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u632

def r803 : Route 9 := (fun mask => (mask,id))

def c803 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 5 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u803 : Upper (D 4) (R 4) [10,96,384] 13 := by
  apply FastRouting.sound _ _ [10,96,384] 13 (by decide) (choices 2) [3,5,6,17,18,20] r803 c803
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m803_3
  · exact m803_5
  · exact m803_6
  · exact m803_17
  · exact m803_18
  · exact m803_20

theorem m804_3 : Upper (D 4) (R 4) [24,33,66,3] 13 :=
  permutation_upper _ _ _ [6,17,34,68] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u584

theorem m804_5 : Upper (D 4) (R 4) [24,33,66,5] 13 :=
  permutation_upper _ _ _ [6,17,40,66] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u588

theorem m804_6 : Upper (D 4) (R 4) [24,33,66,6] 13 :=
  permutation_upper _ _ _ [6,36,72,17] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u662

theorem m804_17 : Upper (D 4) (R 4) [24,33,66,17] 13 :=
  permutation_upper _ _ _ [18,17,33,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u696

theorem m804_18 : Upper (D 4) (R 4) [24,33,66,18] 13 :=
  permutation_upper _ _ _ [18,20,33,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u701

theorem m804_20 : Upper (D 4) (R 4) [24,33,66,20] 13 :=
  permutation_upper _ _ _ [18,20,40,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u703

theorem m804_129 : Upper (D 4) (R 4) [24,33,66,129] 13 :=
  permutation_upper _ _ _ [18,33,65,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u709

theorem m804_130 : Upper (D 4) (R 4) [24,33,66,130] 13 :=
  permutation_upper _ _ _ [18,36,65,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u716

theorem m804_132 : Upper (D 4) (R 4) [24,33,66,132] 13 :=
  permutation_upper _ _ _ [18,36,72,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u721

theorem m804_144 : Upper (D 4) (R 4) [24,33,66,144] 13 :=
  permutation_upper _ _ _ [18,48,65,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u728

theorem m804_384 : Upper (D 4) (R 4) [24,33,66,384] 13 :=
  permutation_upper _ _ _ [18,96,129,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u733

def r804 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c804 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u804 : Upper (D 4) (R 4) [24,33,66] 13 := by
  apply FastRouting.sound _ _ [24,33,66] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r804 c804
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m804_3
  · exact m804_5
  · exact m804_6
  · exact m804_17
  · exact m804_18
  · exact m804_20
  · exact m804_129
  · exact m804_130
  · exact m804_132
  · exact m804_144
  · exact m804_384

theorem m805_3 : Upper (D 4) (R 4) [24,33,192,3] 13 :=
  permutation_upper _ _ _ [6,17,34,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u585

theorem m805_5 : Upper (D 4) (R 4) [24,33,192,5] 13 :=
  permutation_upper _ _ _ [6,17,96,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u595

theorem m805_6 : Upper (D 4) (R 4) [24,33,192,6] 13 :=
  permutation_upper _ _ _ [6,40,192,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u682

theorem m805_17 : Upper (D 4) (R 4) [24,33,192,17] 13 :=
  permutation_upper _ _ _ [18,17,33,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u697

theorem m805_18 : Upper (D 4) (R 4) [24,33,192,18] 13 :=
  permutation_upper _ _ _ [18,20,33,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u702

theorem m805_20 : Upper (D 4) (R 4) [24,33,192,20] 13 :=
  permutation_upper _ _ _ [18,20,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u706

theorem m805_257 : Upper (D 4) (R 4) [24,33,192,257] 13 :=
  permutation_upper _ _ _ [18,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u710

theorem m805_258 : Upper (D 4) (R 4) [24,33,192,258] 13 :=
  permutation_upper _ _ _ [18,36,65,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u717

theorem m805_260 : Upper (D 4) (R 4) [24,33,192,260] 13 :=
  permutation_upper _ _ _ [18,36,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u725

theorem m805_272 : Upper (D 4) (R 4) [24,33,192,272] 13 :=
  permutation_upper _ _ _ [18,48,65,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u729

def r805 : Route 9 := (fun mask => (mask,id))

def c805 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u805 : Upper (D 4) (R 4) [24,33,192] 13 := by
  apply FastRouting.sound _ _ [24,33,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r805 c805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m805_3
  · exact m805_5
  · exact m805_6
  · exact m805_17
  · exact m805_18
  · exact m805_20
  · exact m805_257
  · exact m805_258
  · exact m805_260
  · exact m805_272

theorem m806_3 : Upper (D 4) (R 4) [24,36,66,3] 13 :=
  permutation_upper _ _ _ [6,17,40,68] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u589

theorem m806_5 : Upper (D 4) (R 4) [24,36,66,5] 13 :=
  permutation_upper _ _ _ [6,17,40,68] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u589

theorem m806_6 : Upper (D 4) (R 4) [24,36,66,6] 13 :=
  permutation_upper _ _ _ [6,36,66,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u659

theorem m806_17 : Upper (D 4) (R 4) [24,36,66,17] 13 :=
  permutation_upper _ _ _ [18,17,40,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u698

theorem m806_18 : Upper (D 4) (R 4) [24,36,66,18] 13 :=
  permutation_upper _ _ _ [18,20,40,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u704

theorem m806_20 : Upper (D 4) (R 4) [24,36,66,20] 13 :=
  permutation_upper _ _ _ [18,20,40,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u704

theorem m806_129 : Upper (D 4) (R 4) [24,36,66,129] 13 :=
  permutation_upper _ _ _ [18,33,72,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u713

theorem m806_130 : Upper (D 4) (R 4) [24,36,66,130] 13 :=
  permutation_upper _ _ _ [18,36,72,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u723

theorem m806_132 : Upper (D 4) (R 4) [24,36,66,132] 13 :=
  permutation_upper _ _ _ [18,36,72,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u723

theorem m806_144 : Upper (D 4) (R 4) [24,36,66,144] 13 :=
  permutation_upper _ _ _ [18,48,72,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u730

theorem m806_384 : Upper (D 4) (R 4) [24,36,66,384] 13 :=
  permutation_upper _ _ _ [18,96,136,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u735

def r806 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c806 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u806 : Upper (D 4) (R 4) [24,36,66] 13 := by
  apply FastRouting.sound _ _ [24,36,66] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r806 c806
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m806_3
  · exact m806_5
  · exact m806_6
  · exact m806_17
  · exact m806_18
  · exact m806_20
  · exact m806_129
  · exact m806_130
  · exact m806_132
  · exact m806_144
  · exact m806_384

theorem m807_3 : Upper (D 4) (R 4) [24,36,192,3] 13 :=
  permutation_upper _ _ _ [6,17,40,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u590

theorem m807_5 : Upper (D 4) (R 4) [24,36,192,5] 13 :=
  permutation_upper _ _ _ [6,17,96,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u596

theorem m807_6 : Upper (D 4) (R 4) [24,36,192,6] 13 :=
  permutation_upper _ _ _ [6,36,192,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u668

theorem m807_17 : Upper (D 4) (R 4) [24,36,192,17] 13 :=
  permutation_upper _ _ _ [18,17,40,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u699

theorem m807_18 : Upper (D 4) (R 4) [24,36,192,18] 13 :=
  permutation_upper _ _ _ [18,20,40,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u705

theorem m807_20 : Upper (D 4) (R 4) [24,36,192,20] 13 :=
  permutation_upper _ _ _ [18,20,96,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u707

theorem m807_257 : Upper (D 4) (R 4) [24,36,192,257] 13 :=
  permutation_upper _ _ _ [18,33,72,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u714

theorem m807_258 : Upper (D 4) (R 4) [24,36,192,258] 13 :=
  permutation_upper _ _ _ [18,36,72,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u724

theorem m807_260 : Upper (D 4) (R 4) [24,36,192,260] 13 :=
  permutation_upper _ _ _ [18,36,192,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u727

theorem m807_272 : Upper (D 4) (R 4) [24,36,192,272] 13 :=
  permutation_upper _ _ _ [18,48,72,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u731

def r807 : Route 9 := (fun mask => (mask,id))

def c807 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u807 : Upper (D 4) (R 4) [24,36,192] 13 := by
  apply FastRouting.sound _ _ [24,36,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r807 c807
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m807_3
  · exact m807_5
  · exact m807_6
  · exact m807_17
  · exact m807_18
  · exact m807_20
  · exact m807_257
  · exact m807_258
  · exact m807_260
  · exact m807_272

theorem m808_3 : Upper (D 4) (R 4) [24,96,384,3] 13 :=
  permutation_upper _ _ _ [6,17,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u597

theorem m808_5 : Upper (D 4) (R 4) [24,96,384,5] 13 :=
  permutation_upper _ _ _ [6,17,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u597

theorem m808_6 : Upper (D 4) (R 4) [24,96,384,6] 13 :=
  permutation_upper _ _ _ [6,96,384,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u694

theorem m808_17 : Upper (D 4) (R 4) [24,96,384,17] 13 :=
  permutation_upper _ _ _ [18,17,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u700

theorem m808_18 : Upper (D 4) (R 4) [24,96,384,18] 13 :=
  permutation_upper _ _ _ [18,20,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u708

theorem m808_20 : Upper (D 4) (R 4) [24,96,384,20] 13 :=
  permutation_upper _ _ _ [18,20,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u708

def r808 : Route 9 := (fun mask => (mask,id))

def c808 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 5 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u808 : Upper (D 4) (R 4) [24,96,384] 13 := by
  apply FastRouting.sound _ _ [24,96,384] 13 (by decide) (choices 2) [3,5,6,17,18,20] r808 c808
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m808_3
  · exact m808_5
  · exact m808_6
  · exact m808_17
  · exact m808_18
  · exact m808_20

theorem m809_6 : Upper (D 4) (R 4) [34,65,129,6] 13 :=
  permutation_upper _ _ _ [6,40,72,130] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u672

theorem m809_18 : Upper (D 4) (R 4) [34,65,129,18] 13 :=
  permutation_upper _ _ _ [18,36,66,132] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u719

theorem m809_20 : Upper (D 4) (R 4) [34,65,129,20] 13 :=
  permutation_upper _ _ _ [18,36,72,132] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u723

def r809 : Route 9 := (fun mask => (mask,id))

def c809 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u809 : Upper (D 4) (R 4) [34,65,129] 13 := by
  apply FastRouting.sound _ _ [34,65,129] 13 (by decide) (choices 2) [6,18,20,258,260,272] r809 c809
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m809_6
  · exact m809_18
  · exact m809_20
  · exact u736
  · exact u737
  · exact u738

theorem m810_3 : Upper (D 4) (R 4) [34,65,136,3] 13 :=
  permutation_upper _ _ _ [6,36,66,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u660

theorem m810_5 : Upper (D 4) (R 4) [34,65,136,5] 13 :=
  permutation_upper _ _ _ [6,33,72,132] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u644

theorem m810_6 : Upper (D 4) (R 4) [34,65,136,6] 13 :=
  permutation_upper _ _ _ [6,33,72,132] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u644

theorem m810_17 : Upper (D 4) (R 4) [34,65,136,17] 13 :=
  permutation_upper _ _ _ [18,36,66,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u718

theorem m810_18 : Upper (D 4) (R 4) [34,65,136,18] 13 :=
  permutation_upper _ _ _ [18,36,66,129] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u718

theorem m810_20 : Upper (D 4) (R 4) [34,65,136,20] 13 :=
  permutation_upper _ _ _ [18,33,72,132] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u713

theorem m810_257 : Upper (D 4) (R 4) [34,65,136,257] 13 :=
  permutation_upper _ _ _ [34,65,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u737

theorem m810_258 : Upper (D 4) (R 4) [34,65,136,258] 13 :=
  permutation_upper _ _ _ [34,65,129,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u737

def r810 : Route 9 := (fun mask => (mask,id))

def c810 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u810 : Upper (D 4) (R 4) [34,65,136] 13 := by
  apply FastRouting.sound _ _ [34,65,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r810 c810
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m810_3
  · exact m810_5
  · exact m810_6
  · exact m810_17
  · exact m810_18
  · exact m810_20
  · exact m810_257
  · exact m810_258
  · exact u739
  · exact u740

theorem m811_3 : Upper (D 4) (R 4) [34,65,384,3] 13 :=
  permutation_upper _ _ _ [6,36,66,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u661

theorem m811_5 : Upper (D 4) (R 4) [34,65,384,5] 13 :=
  permutation_upper _ _ _ [6,40,192,258] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u686

theorem m811_6 : Upper (D 4) (R 4) [34,65,384,6] 13 :=
  permutation_upper _ _ _ [6,40,192,258] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u686

theorem m811_17 : Upper (D 4) (R 4) [34,65,384,17] 13 :=
  permutation_upper _ _ _ [18,36,66,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u720

theorem m811_18 : Upper (D 4) (R 4) [34,65,384,18] 13 :=
  permutation_upper _ _ _ [18,36,66,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u720

theorem m811_20 : Upper (D 4) (R 4) [34,65,384,20] 13 :=
  permutation_upper _ _ _ [18,96,136,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u735

def r811 : Route 9 := (fun mask => (mask,id))

def c811 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 5 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u811 : Upper (D 4) (R 4) [34,65,384] 13 := by
  apply FastRouting.sound _ _ [34,65,384] 13 (by decide) (choices 2) [3,5,6,17,18,20] r811 c811
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m811_3
  · exact m811_5
  · exact m811_6
  · exact m811_17
  · exact m811_18
  · exact m811_20

theorem m812_3 : Upper (D 4) (R 4) [34,68,129,3] 13 :=
  permutation_upper _ _ _ [6,36,72,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u664

theorem m812_5 : Upper (D 4) (R 4) [34,68,129,5] 13 :=
  permutation_upper _ _ _ [6,36,72,130] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u664

theorem m812_6 : Upper (D 4) (R 4) [34,68,129,6] 13 :=
  permutation_upper _ _ _ [6,36,72,130] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u664

theorem m812_17 : Upper (D 4) (R 4) [34,68,129,17] 13 :=
  permutation_upper _ _ _ [18,36,72,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u722

theorem m812_18 : Upper (D 4) (R 4) [34,68,129,18] 13 :=
  permutation_upper _ _ _ [18,36,72,130] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u722

theorem m812_20 : Upper (D 4) (R 4) [34,68,129,20] 13 :=
  permutation_upper _ _ _ [18,36,72,130] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u722

theorem m812_258 : Upper (D 4) (R 4) [34,68,129,258] 13 :=
  permutation_upper _ _ _ [34,68,129,257] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u741

theorem m812_260 : Upper (D 4) (R 4) [34,68,129,260] 13 :=
  permutation_upper _ _ _ [34,68,129,257] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u741

def r812 : Route 9 := (fun mask => (mask,id))

def c812 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u812 : Upper (D 4) (R 4) [34,68,129] 13 := by
  apply FastRouting.sound _ _ [34,68,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r812 c812
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m812_3
  · exact m812_5
  · exact m812_6
  · exact m812_17
  · exact m812_18
  · exact m812_20
  · exact u741
  · exact m812_258
  · exact m812_260
  · exact u742

theorem m813_3 : Upper (D 4) (R 4) [34,68,136,3] 13 :=
  permutation_upper _ _ _ [6,36,72,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u663

theorem m813_5 : Upper (D 4) (R 4) [34,68,136,5] 13 :=
  permutation_upper _ _ _ [6,33,72,130] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u643

theorem m813_6 : Upper (D 4) (R 4) [34,68,136,6] 13 :=
  permutation_upper _ _ _ [6,33,66,132] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u636

theorem m813_17 : Upper (D 4) (R 4) [34,68,136,17] 13 :=
  permutation_upper _ _ _ [18,36,72,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u721

theorem m813_18 : Upper (D 4) (R 4) [34,68,136,18] 13 :=
  permutation_upper _ _ _ [18,36,65,130] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u715

theorem m813_20 : Upper (D 4) (R 4) [34,68,136,20] 13 :=
  permutation_upper _ _ _ [18,33,66,132] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u711

theorem m813_258 : Upper (D 4) (R 4) [34,68,136,258] 13 :=
  permutation_upper _ _ _ [34,68,129,257] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u741

theorem m813_260 : Upper (D 4) (R 4) [34,68,136,260] 13 :=
  permutation_upper _ _ _ [34,65,129,260] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 6 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 8 | 6 => 7 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u737

def r813 : Route 9 := (fun mask => (mask,id))

def c813 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u813 : Upper (D 4) (R 4) [34,68,136] 13 := by
  apply FastRouting.sound _ _ [34,68,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r813 c813
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m813_3
  · exact m813_5
  · exact m813_6
  · exact m813_17
  · exact m813_18
  · exact m813_20
  · exact u743
  · exact m813_258
  · exact m813_260
  · exact u744

theorem m814_3 : Upper (D 4) (R 4) [34,68,384,3] 13 :=
  permutation_upper _ _ _ [6,36,72,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u665

theorem m814_5 : Upper (D 4) (R 4) [34,68,384,5] 13 :=
  permutation_upper _ _ _ [6,40,192,260] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u687

theorem m814_6 : Upper (D 4) (R 4) [34,68,384,6] 13 :=
  permutation_upper _ _ _ [6,36,192,258] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u670

theorem m814_17 : Upper (D 4) (R 4) [34,68,384,17] 13 :=
  permutation_upper _ _ _ [18,36,72,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u724

theorem m814_18 : Upper (D 4) (R 4) [34,68,384,18] 13 :=
  permutation_upper _ _ _ [18,36,192,258] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u726

theorem m814_20 : Upper (D 4) (R 4) [34,68,384,20] 13 :=
  permutation_upper _ _ _ [18,96,130,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 6 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 7 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u734

def r814 : Route 9 := (fun mask => (mask,id))

def c814 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 5 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u814 : Upper (D 4) (R 4) [34,68,384] 13 := by
  apply FastRouting.sound _ _ [34,68,384] 13 (by decide) (choices 2) [3,5,6,17,18,20] r814 c814
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m814_3
  · exact m814_5
  · exact m814_6
  · exact m814_17
  · exact m814_18
  · exact m814_20

theorem m815_3 : Upper (D 4) (R 4) [34,72,384,3] 13 :=
  permutation_upper _ _ _ [6,33,66,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u637

theorem m815_5 : Upper (D 4) (R 4) [34,72,384,5] 13 :=
  permutation_upper _ _ _ [6,40,192,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u685

theorem m815_6 : Upper (D 4) (R 4) [34,72,384,6] 13 :=
  permutation_upper _ _ _ [6,33,192,258] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u656

theorem m815_17 : Upper (D 4) (R 4) [34,72,384,17] 13 :=
  permutation_upper _ _ _ [18,36,65,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u717

theorem m815_18 : Upper (D 4) (R 4) [34,72,384,18] 13 :=
  permutation_upper _ _ _ [18,33,66,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u712

theorem m815_20 : Upper (D 4) (R 4) [34,72,384,20] 13 :=
  permutation_upper _ _ _ [18,96,129,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 6 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 7 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u733

def r815 : Route 9 := (fun mask => (mask,id))

def c815 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 5 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u815 : Upper (D 4) (R 4) [34,72,384] 13 := by
  apply FastRouting.sound _ _ [34,72,384] 13 (by decide) (choices 2) [3,5,6,17,18,20] r815 c815
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m815_3
  · exact m815_5
  · exact m815_6
  · exact m815_17
  · exact m815_18
  · exact m815_20

theorem m816_5 : Upper (D 4) (R 4) [34,192,258,5] 13 :=
  permutation_upper _ _ _ [6,40,72,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u673

theorem m816_17 : Upper (D 4) (R 4) [34,192,258,17] 13 :=
  permutation_upper _ _ _ [18,36,192,260] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u727

theorem m816_20 : Upper (D 4) (R 4) [34,192,258,20] 13 :=
  permutation_upper _ _ _ [18,36,192,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u727

def r816 : Route 9 := (fun mask => (mask,id))

def c816 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 5 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u816 : Upper (D 4) (R 4) [34,192,258] 13 := by
  apply FastRouting.sound _ _ [34,192,258] 13 (by decide) (choices 2) [5,17,20] r816 c816
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m816_5
  · exact m816_17
  · exact m816_20

theorem m817_3 : Upper (D 4) (R 4) [34,192,264,3] 13 :=
  permutation_upper _ _ _ [6,36,192,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u669

theorem m817_5 : Upper (D 4) (R 4) [34,192,264,5] 13 :=
  permutation_upper _ _ _ [6,33,72,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u646

theorem m817_6 : Upper (D 4) (R 4) [34,192,264,6] 13 :=
  permutation_upper _ _ _ [6,33,192,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u657

theorem m817_17 : Upper (D 4) (R 4) [34,192,264,17] 13 :=
  permutation_upper _ _ _ [18,36,192,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u725

theorem m817_18 : Upper (D 4) (R 4) [34,192,264,18] 13 :=
  permutation_upper _ _ _ [18,96,129,258] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u732

theorem m817_20 : Upper (D 4) (R 4) [34,192,264,20] 13 :=
  permutation_upper _ _ _ [18,33,72,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u714

def r817 : Route 9 := (fun mask => (mask,id))

def c817 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 5 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u817 : Upper (D 4) (R 4) [34,192,264] 13 := by
  apply FastRouting.sound _ _ [34,192,264] 13 (by decide) (choices 2) [3,5,6,17,18,20] r817 c817
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m817_3
  · exact m817_5
  · exact m817_6
  · exact m817_17
  · exact m817_18
  · exact m817_20

def b818 : PairBound 9 := { available := 507, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 511 507 507 507 507 507 507), lower := (rows 7 7 4 8 16 32 64 128 256), losses := [] }

theorem u818 : Upper (D 4) (R 4) [6,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b818
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m819_3 : Upper (D 4) (R 4) [6,9,3] 13 :=
  permutation_upper _ _ _ [6,5,9] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u745

def r819 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 257 => (33,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 258 => (34,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 264 => (40,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 272 => (48,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (96,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 384 => (96,(fun i => match i.val with | 5 => 7 | 6 => 8 | 7 => 5 | 8 => 6 | _ => i)) | _ => (mask,id))

def c819 : Nat → Fin 9 := (fun _ => 0)

theorem u819 : Upper (D 4) (R 4) [6,9] 13 := by
  apply FastRouting.sound _ _ [6,9] 13 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48,96] r819 c819
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m819_3
  · exact u750
  · exact u751
  · exact u752
  · exact u753
  · exact u754
  · exact u755
  · exact u756
  · exact u757
  · exact u758
  · exact u759

def b820 : PairBound 9 := { available := 507, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2)], upper := (rows 7 14 511 507 507 507 507 507 507), lower := (rows 7 14 4 8 16 32 64 128 256), losses := [] }

theorem u820 : Upper (D 4) (R 4) [6,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b820
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m821_3 : Upper (D 4) (R 4) [6,24,3] 13 :=
  permutation_upper _ _ _ [6,5,24] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u746

theorem m821_9 : Upper (D 4) (R 4) [6,24,9] 13 :=
  permutation_upper _ _ _ [6,9,24] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u754

theorem m821_10 : Upper (D 4) (R 4) [6,24,10] 13 :=
  permutation_upper _ _ _ [6,12,24] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u760

def r821 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 257 => (33,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 258 => (34,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 264 => (40,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 7 | 7 => 5 | _ => i)) | 272 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 8 | 8 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (96,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 384 => (96,(fun i => match i.val with | 5 => 7 | 6 => 8 | 7 => 5 | 8 => 6 | _ => i)) | _ => (mask,id))

def c821 : Nat → Fin 9 := (fun _ => 0)

theorem u821 : Upper (D 4) (R 4) [6,24] 13 := by
  apply FastRouting.sound _ _ [6,24] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,96] r821 c821
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m821_3
  · exact m821_9
  · exact m821_10
  · exact u765
  · exact u766
  · exact u767
  · exact u768
  · exact u769

theorem m822_3 : Upper (D 4) (R 4) [6,33,3] 13 :=
  permutation_upper _ _ _ [6,5,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u747

theorem m822_9 : Upper (D 4) (R 4) [6,33,9] 13 :=
  permutation_upper _ _ _ [6,9,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u755

theorem m822_10 : Upper (D 4) (R 4) [6,33,10] 13 :=
  permutation_upper _ _ _ [6,12,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u761

theorem m822_24 : Upper (D 4) (R 4) [6,33,24] 13 :=
  permutation_upper _ _ _ [6,24,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u766

def r822 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 264 => (72,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 272 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c822 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u822 : Upper (D 4) (R 4) [6,33] 13 := by
  apply FastRouting.sound _ _ [6,33] 13 (by decide) (choices 2) [3,9,10,24,65,66,72,192] r822 c822
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m822_3
  · exact m822_9
  · exact m822_10
  · exact m822_24
  · exact u770
  · exact u771
  · exact u772
  · exact u773

def b823 : PairBound 9 := { available := 475, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 479 475 475 507 475 475 475), lower := (rows 7 38 4 8 16 32 64 128 256), losses := [] }

theorem u823 : Upper (D 4) (R 4) [6,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b823
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m824_3 : Upper (D 4) (R 4) [6,40,3] 13 :=
  permutation_upper _ _ _ [6,5,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u748

theorem m824_9 : Upper (D 4) (R 4) [6,40,9] 13 :=
  permutation_upper _ _ _ [6,9,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u757

theorem m824_10 : Upper (D 4) (R 4) [6,40,10] 13 :=
  permutation_upper _ _ _ [6,12,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u762

theorem m824_17 : Upper (D 4) (R 4) [6,40,17] 13 :=
  permutation_upper _ _ _ [6,9,48] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u758

theorem m824_18 : Upper (D 4) (R 4) [6,40,18] 13 :=
  permutation_upper _ _ _ [6,12,48] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u763

theorem m824_24 : Upper (D 4) (R 4) [6,40,24] 13 :=
  permutation_upper _ _ _ [6,24,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u768

theorem m824_65 : Upper (D 4) (R 4) [6,40,65] 13 :=
  permutation_upper _ _ _ [6,33,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u772

theorem m824_66 : Upper (D 4) (R 4) [6,40,66] 13 :=
  permutation_upper _ _ _ [6,36,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u775

def r824 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 264 => (72,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c824 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u824 : Upper (D 4) (R 4) [6,40] 13 := by
  apply FastRouting.sound _ _ [6,40] 13 (by decide) (choices 2) [3,9,10,17,18,24,65,66,72,80,192] r824 c824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m824_3
  · exact m824_9
  · exact m824_10
  · exact m824_17
  · exact m824_18
  · exact m824_24
  · exact m824_65
  · exact m824_66
  · exact u777
  · exact u778
  · exact u779

theorem m825_3 : Upper (D 4) (R 4) [6,96,3] 13 :=
  permutation_upper _ _ _ [6,5,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u749

theorem m825_9 : Upper (D 4) (R 4) [6,96,9] 13 :=
  permutation_upper _ _ _ [6,9,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u759

theorem m825_10 : Upper (D 4) (R 4) [6,96,10] 13 :=
  permutation_upper _ _ _ [6,12,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u764

theorem m825_24 : Upper (D 4) (R 4) [6,96,24] 13 :=
  permutation_upper _ _ _ [6,24,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u769

theorem m825_129 : Upper (D 4) (R 4) [6,96,129] 13 :=
  permutation_upper _ _ _ [6,33,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u773

theorem m825_130 : Upper (D 4) (R 4) [6,96,130] 13 :=
  permutation_upper _ _ _ [6,36,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u776

theorem m825_136 : Upper (D 4) (R 4) [6,96,136] 13 :=
  permutation_upper _ _ _ [6,40,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u779

def r825 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c825 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u825 : Upper (D 4) (R 4) [6,96] 13 := by
  apply FastRouting.sound _ _ [6,96] 13 (by decide) (choices 2) [3,9,10,24,129,130,136,384] r825 c825
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m825_3
  · exact m825_9
  · exact m825_10
  · exact m825_24
  · exact m825_129
  · exact m825_130
  · exact m825_136
  · exact u780

theorem m826_3 : Upper (D 4) (R 4) [12,33,3] 13 :=
  permutation_upper _ _ _ [6,9,34] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u756

theorem m826_9 : Upper (D 4) (R 4) [12,33,9] 13 :=
  permutation_upper _ _ _ [10,9,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u781

theorem m826_10 : Upper (D 4) (R 4) [12,33,10] 13 :=
  permutation_upper _ _ _ [10,12,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u783

theorem m826_17 : Upper (D 4) (R 4) [12,33,17] 13 :=
  permutation_upper _ _ _ [10,17,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u785

theorem m826_18 : Upper (D 4) (R 4) [12,33,18] 13 :=
  permutation_upper _ _ _ [10,20,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u787

theorem m826_24 : Upper (D 4) (R 4) [12,33,24] 13 :=
  permutation_upper _ _ _ [10,24,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u789

theorem m826_65 : Upper (D 4) (R 4) [12,33,65] 13 :=
  permutation_upper _ _ _ [10,33,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u791

theorem m826_66 : Upper (D 4) (R 4) [12,33,66] 13 :=
  permutation_upper _ _ _ [10,36,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u794

theorem m826_72 : Upper (D 4) (R 4) [12,33,72] 13 :=
  permutation_upper _ _ _ [10,40,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u797

theorem m826_80 : Upper (D 4) (R 4) [12,33,80] 13 :=
  permutation_upper _ _ _ [10,48,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u799

theorem m826_192 : Upper (D 4) (R 4) [12,33,192] 13 :=
  permutation_upper _ _ _ [10,96,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u801

def r826 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 264 => (72,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c826 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u826 : Upper (D 4) (R 4) [12,33] 13 := by
  apply FastRouting.sound _ _ [12,33] 13 (by decide) (choices 2) [3,9,10,17,18,24,65,66,72,80,192] r826 c826
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m826_3
  · exact m826_9
  · exact m826_10
  · exact m826_17
  · exact m826_18
  · exact m826_24
  · exact m826_65
  · exact m826_66
  · exact m826_72
  · exact m826_80
  · exact m826_192

theorem m827_3 : Upper (D 4) (R 4) [12,96,3] 13 :=
  permutation_upper _ _ _ [6,9,96] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u759

theorem m827_9 : Upper (D 4) (R 4) [12,96,9] 13 :=
  permutation_upper _ _ _ [10,9,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u782

theorem m827_10 : Upper (D 4) (R 4) [12,96,10] 13 :=
  permutation_upper _ _ _ [10,12,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u784

theorem m827_17 : Upper (D 4) (R 4) [12,96,17] 13 :=
  permutation_upper _ _ _ [10,17,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u786

theorem m827_18 : Upper (D 4) (R 4) [12,96,18] 13 :=
  permutation_upper _ _ _ [10,20,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u788

theorem m827_24 : Upper (D 4) (R 4) [12,96,24] 13 :=
  permutation_upper _ _ _ [10,24,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u790

theorem m827_129 : Upper (D 4) (R 4) [12,96,129] 13 :=
  permutation_upper _ _ _ [10,33,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u793

theorem m827_130 : Upper (D 4) (R 4) [12,96,130] 13 :=
  permutation_upper _ _ _ [10,36,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u796

theorem m827_136 : Upper (D 4) (R 4) [12,96,136] 13 :=
  permutation_upper _ _ _ [10,40,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u798

theorem m827_144 : Upper (D 4) (R 4) [12,96,144] 13 :=
  permutation_upper _ _ _ [10,48,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u800

theorem m827_384 : Upper (D 4) (R 4) [12,96,384] 13 :=
  permutation_upper _ _ _ [10,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u803

def r827 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c827 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u827 : Upper (D 4) (R 4) [12,96] 13 := by
  apply FastRouting.sound _ _ [12,96] 13 (by decide) (choices 2) [3,9,10,17,18,24,129,130,136,144,384] r827 c827
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m827_3
  · exact m827_9
  · exact m827_10
  · exact m827_17
  · exact m827_18
  · exact m827_24
  · exact m827_129
  · exact m827_130
  · exact m827_136
  · exact m827_144
  · exact m827_384

theorem m828_3 : Upper (D 4) (R 4) [34,65,3] 13 :=
  permutation_upper _ _ _ [6,36,66] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u774

theorem m828_9 : Upper (D 4) (R 4) [34,65,9] 13 :=
  permutation_upper _ _ _ [10,36,66] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u795

theorem m828_10 : Upper (D 4) (R 4) [34,65,10] 13 :=
  permutation_upper _ _ _ [10,36,66] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u795

theorem m828_24 : Upper (D 4) (R 4) [34,65,24] 13 :=
  permutation_upper _ _ _ [24,36,66] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u806

theorem m828_130 : Upper (D 4) (R 4) [34,65,130] 13 :=
  permutation_upper _ _ _ [34,65,129] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u809

def r828 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c828 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u828 : Upper (D 4) (R 4) [34,65] 13 := by
  apply FastRouting.sound _ _ [34,65] 13 (by decide) (choices 2) [3,9,10,24,129,130,136,384] r828 c828
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m828_3
  · exact m828_9
  · exact m828_10
  · exact m828_24
  · exact u809
  · exact m828_130
  · exact u810
  · exact u811

theorem m829_3 : Upper (D 4) (R 4) [34,68,3] 13 :=
  permutation_upper _ _ _ [6,33,66] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u771

theorem m829_9 : Upper (D 4) (R 4) [34,68,9] 13 :=
  permutation_upper _ _ _ [10,36,65] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u794

theorem m829_10 : Upper (D 4) (R 4) [34,68,10] 13 :=
  permutation_upper _ _ _ [10,33,66] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u792

theorem m829_24 : Upper (D 4) (R 4) [34,68,24] 13 :=
  permutation_upper _ _ _ [24,33,66] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u804

theorem m829_130 : Upper (D 4) (R 4) [34,68,130] 13 :=
  permutation_upper _ _ _ [34,65,129] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u809

def r829 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c829 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u829 : Upper (D 4) (R 4) [34,68] 13 := by
  apply FastRouting.sound _ _ [34,68] 13 (by decide) (choices 2) [3,9,10,24,129,130,136,384] r829 c829
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m829_3
  · exact m829_9
  · exact m829_10
  · exact m829_24
  · exact u812
  · exact m829_130
  · exact u813
  · exact u814

theorem m830_3 : Upper (D 4) (R 4) [34,192,3] 13 :=
  permutation_upper _ _ _ [6,36,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u776

theorem m830_9 : Upper (D 4) (R 4) [34,192,9] 13 :=
  permutation_upper _ _ _ [10,36,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u796

theorem m830_10 : Upper (D 4) (R 4) [34,192,10] 13 :=
  permutation_upper _ _ _ [10,96,130] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u802

theorem m830_24 : Upper (D 4) (R 4) [34,192,24] 13 :=
  permutation_upper _ _ _ [24,36,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u807

theorem m830_257 : Upper (D 4) (R 4) [34,192,257] 13 :=
  permutation_upper _ _ _ [34,68,384] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u814

def r830 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

def c830 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u830 : Upper (D 4) (R 4) [34,192] 13 := by
  apply FastRouting.sound _ _ [34,192] 13 (by decide) (choices 2) [3,9,10,24,257,258,264] r830 c830
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m830_3
  · exact m830_9
  · exact m830_10
  · exact m830_24
  · exact m830_257
  · exact u816
  · exact u817

theorem m831_3 : Upper (D 4) (R 4) [36,192,3] 13 :=
  permutation_upper _ _ _ [6,33,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u773

theorem m831_9 : Upper (D 4) (R 4) [36,192,9] 13 :=
  permutation_upper _ _ _ [10,33,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u793

theorem m831_10 : Upper (D 4) (R 4) [36,192,10] 13 :=
  permutation_upper _ _ _ [10,96,129] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u801

theorem m831_24 : Upper (D 4) (R 4) [36,192,24] 13 :=
  permutation_upper _ _ _ [24,33,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u805

theorem m831_257 : Upper (D 4) (R 4) [36,192,257] 13 :=
  permutation_upper _ _ _ [34,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u811

theorem m831_258 : Upper (D 4) (R 4) [36,192,258] 13 :=
  permutation_upper _ _ _ [34,68,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u814

theorem m831_264 : Upper (D 4) (R 4) [36,192,264] 13 :=
  permutation_upper _ _ _ [34,72,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u815

def r831 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

def c831 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u831 : Upper (D 4) (R 4) [36,192] 13 := by
  apply FastRouting.sound _ _ [36,192] 13 (by decide) (choices 2) [3,9,10,24,257,258,264] r831 c831
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m831_3
  · exact m831_9
  · exact m831_10
  · exact m831_24
  · exact m831_257
  · exact m831_258
  · exact m831_264

theorem m832_3 : Upper (D 4) (R 4) [96,384,3] 13 :=
  permutation_upper _ _ _ [6,96,384] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u780

theorem m832_9 : Upper (D 4) (R 4) [96,384,9] 13 :=
  permutation_upper _ _ _ [10,96,384] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u803

theorem m832_10 : Upper (D 4) (R 4) [96,384,10] 13 :=
  permutation_upper _ _ _ [10,96,384] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u803

theorem m832_24 : Upper (D 4) (R 4) [96,384,24] 13 :=
  permutation_upper _ _ _ [24,96,384] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u808

def r832 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

def c832 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 48 => 5 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u832 : Upper (D 4) (R 4) [96,384] 13 := by
  apply FastRouting.sound _ _ [96,384] 13 (by decide) (choices 2) [3,9,10,24] r832 c832
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m832_3
  · exact m832_9
  · exact m832_10
  · exact m832_24

def r833 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 257 => (33,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 132 => (36,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 260 => (36,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 264 => (40,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 7 | 7 => 5 | _ => i)) | 272 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 8 | 8 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (96,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 384 => (96,(fun i => match i.val with | 5 => 7 | 6 => 8 | 7 => 5 | 8 => 6 | _ => i)) | _ => (mask,id))

def c833 : Nat → Fin 9 := (fun _ => 0)

theorem u833 : Upper (D 4) (R 4) [6] 13 := by
  apply FastRouting.sound _ _ [6] 13 (by decide) (choices 2) [5,9,12,24,33,36,40,96] r833 c833
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u818
  · exact u819
  · exact u820
  · exact u821
  · exact u822
  · exact u823
  · exact u824
  · exact u825

theorem m834_5 : Upper (D 4) (R 4) [34,5] 13 :=
  permutation_upper _ _ _ [6,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u822

theorem m834_12 : Upper (D 4) (R 4) [34,12] 13 :=
  permutation_upper _ _ _ [12,33] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u826

def r834 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 17 => (5,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 260 => (68,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 24 => (12,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 72 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 136 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 264 => (68,(fun i => match i.val with | 2 => 3 | 3 => 2 | 6 => 8 | 8 => 6 | _ => i)) | 80 => (68,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 144 => (68,(fun i => match i.val with | 2 => 4 | 4 => 2 | 6 => 7 | 7 => 6 | _ => i)) | 272 => (68,(fun i => match i.val with | 2 => 4 | 4 => 2 | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c834 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 36 => 5 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u834 : Upper (D 4) (R 4) [34] 13 := by
  apply FastRouting.sound _ _ [34] 13 (by decide) (choices 2) [5,12,65,68,192] r834 c834
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m834_5
  · exact m834_12
  · exact u828
  · exact u829
  · exact u830

theorem m835_5 : Upper (D 4) (R 4) [96,5] 13 :=
  permutation_upper _ _ _ [6,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u825

theorem m835_12 : Upper (D 4) (R 4) [96,12] 13 :=
  permutation_upper _ _ _ [12,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u827

theorem m835_129 : Upper (D 4) (R 4) [96,129] 13 :=
  permutation_upper _ _ _ [34,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u830

theorem m835_132 : Upper (D 4) (R 4) [96,132] 13 :=
  permutation_upper _ _ _ [36,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u831

def r835 : Route 9 := (fun mask => match mask with | 9 => (5,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 17 => (5,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 20 => (12,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 24 => (12,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 136 => (132,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 264 => (132,(fun i => match i.val with | 2 => 3 | 3 => 2 | 7 => 8 | 8 => 7 | _ => i)) | 144 => (132,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 272 => (132,(fun i => match i.val with | 2 => 4 | 4 => 2 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c835 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u835 : Upper (D 4) (R 4) [96] 13 := by
  apply FastRouting.sound _ _ [96] 13 (by decide) (choices 2) [5,12,129,132,384] r835 c835
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m835_5
  · exact m835_12
  · exact m835_129
  · exact m835_132
  · exact u832

def r836 : Route 9 := (fun mask => match mask with | 10 => (6,(fun i => match i.val with | 2 => 3 | 3 => 2 | _ => i)) | 18 => (6,(fun i => match i.val with | 2 => 4 | 4 => 2 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 258 => (34,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 12 => (6,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 20 => (6,(fun i => match i.val with | 1 => 4 | 4 => 1 | _ => i)) | 36 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | _ => i)) | 68 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 132 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 7 | 7 => 5 | _ => i)) | 260 => (34,(fun i => match i.val with | 1 => 2 | 2 => 1 | 5 => 8 | 8 => 5 | _ => i)) | 24 => (6,(fun i => match i.val with | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | _ => i)) | 40 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | _ => i)) | 72 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 136 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 7 | 7 => 5 | _ => i)) | 264 => (34,(fun i => match i.val with | 1 => 3 | 3 => 1 | 5 => 8 | 8 => 5 | _ => i)) | 48 => (34,(fun i => match i.val with | 1 => 4 | 4 => 1 | _ => i)) | 80 => (34,(fun i => match i.val with | 1 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (34,(fun i => match i.val with | 1 => 4 | 4 => 1 | 5 => 7 | 7 => 5 | _ => i)) | 272 => (34,(fun i => match i.val with | 1 => 4 | 4 => 1 | 5 => 8 | 8 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (96,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 384 => (96,(fun i => match i.val with | 5 => 7 | 6 => 8 | 7 => 5 | 8 => 6 | _ => i)) | _ => (mask,id))

def c836 : Nat → Fin 9 := (fun _ => 0)

theorem u836 : Upper (D 4) (R 4) [] 13 := by
  apply FastRouting.sound _ _ [] 13 (by decide) (choices 2) [6,34,96] r836 c836
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u833
  · exact u834
  · exact u835

#print axioms u836
end Delivery.IrregularNine14.P04
