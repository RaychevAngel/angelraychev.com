import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0479
import IrregularNine14P06C0480
import IrregularNine14P06C0481
import IrregularNine14P06C0482
import IrregularNine14P06C0483

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m40860_3 : Upper (D 6) (R 6) [6,40,48,384,3] 13 :=
  permutation_upper _ _ _ [6,40,48,5,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28794

theorem m40860_5 : Upper (D 6) (R 6) [6,40,48,384,5] 13 :=
  permutation_upper _ _ _ [6,40,48,3,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28790

theorem m40860_6 : Upper (D 6) (R 6) [6,40,48,384,6] 13 :=
  permutation_upper _ _ _ [6,40,48,6,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28798

theorem m40860_65 : Upper (D 6) (R 6) [6,40,48,384,65] 13 :=
  permutation_upper _ _ _ [6,40,48,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28806

theorem m40860_66 : Upper (D 6) (R 6) [6,40,48,384,66] 13 :=
  permutation_upper _ _ _ [6,40,48,68,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28812

theorem m40860_68 : Upper (D 6) (R 6) [6,40,48,384,68] 13 :=
  permutation_upper _ _ _ [6,40,48,66,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28809

def r40860 : Route 9 := (fun mask => (mask,id))

def c40860 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40860 : Upper (D 6) (R 6) [6,40,48,384] 13 := by
  apply FastRouting.sound _ _ [6,40,48,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r40860 c40860
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40860_3
  · exact m40860_5
  · exact m40860_6
  · exact m40860_65
  · exact m40860_66
  · exact m40860_68

def b40861 : PairBound 9 := { available := 485, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 42 84 11 501 485 485 485 485), lower := (rows 7 42 84 11 16 32 64 128 256), losses := [] }

theorem u40861 : Upper (D 6) (R 6) [6,40,80,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40861
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40862 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 42 84 13 499 483 483 483 483), lower := (rows 7 42 84 13 16 32 64 128 256), losses := [] }

theorem u40862 : Upper (D 6) (R 6) [6,40,80,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40862
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40863 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 84 14 497 481 481 481 481), lower := (rows 7 42 84 14 16 32 64 128 256), losses := [] }

theorem u40863 : Upper (D 6) (R 6) [6,40,80,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40863
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40864 : PairBound 9 := { available := 455, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 41 471 487 455 455 455), lower := (rows 7 42 84 41 16 32 64 128 256), losses := [] }

theorem u40864 : Upper (D 6) (R 6) [6,40,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40864
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40865 : PairBound 9 := { available := 453, camps := [{ cop := 5, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 84 42 469 485 453 453 453), lower := (rows 7 42 84 42 16 32 64 128 256), losses := [] }

theorem u40865 : Upper (D 6) (R 6) [6,40,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40865
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40866 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 44 467 483 451 451 451), lower := (rows 7 42 84 44 16 32 64 128 256), losses := [] }

theorem u40866 : Upper (D 6) (R 6) [6,40,80,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40866
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40867_3 : Upper (D 6) (R 6) [6,40,80,65,3] 13 :=
  permutation_upper _ _ _ [6,40,80,5,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28825

theorem m40867_5 : Upper (D 6) (R 6) [6,40,80,65,5] 13 :=
  permutation_upper _ _ _ [6,40,80,3,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28820

theorem m40867_6 : Upper (D 6) (R 6) [6,40,80,65,6] 13 :=
  permutation_upper _ _ _ [6,40,80,6,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28830

def r40867 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40867 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 10 => 3 | 66 => 6 | 12 => 3 | 68 => 6 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u40867 : Upper (D 6) (R 6) [6,40,80,65] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r40867 c40867
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40867_3
  · exact m40867_5
  · exact m40867_6
  · exact u28844
  · exact u28845
  · exact u28846
  · exact u28847
  · exact u28848
  · exact u28849
  · exact u28850
  · exact u28851

def b40868 : PairBound 9 := { available := 421, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 42 84 74 437 421 485 421 421), lower := (rows 7 42 84 74 16 32 64 128 256), losses := [] }

theorem u40868 : Upper (D 6) (R 6) [6,40,80,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40868
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40869 : PairBound 9 := { available := 419, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 7 42 84 76 435 419 483 419 419), lower := (rows 7 42 84 76 16 32 64 128 256), losses := [] }

theorem u40869 : Upper (D 6) (R 6) [6,40,80,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40869
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40870 : PairBound 9 := { available := 391, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 104 407 423 455 391 391), lower := (rows 7 42 84 104 16 32 64 128 256), losses := [] }

theorem u40870 : Upper (D 6) (R 6) [6,40,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40870
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40871_3 : Upper (D 6) (R 6) [6,40,80,129,3] 13 :=
  permutation_upper _ _ _ [6,40,80,5,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28826

theorem m40871_5 : Upper (D 6) (R 6) [6,40,80,129,5] 13 :=
  permutation_upper _ _ _ [6,40,80,3,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28821

theorem m40871_6 : Upper (D 6) (R 6) [6,40,80,129,6] 13 :=
  permutation_upper _ _ _ [6,40,80,6,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28831

theorem m40871_33 : Upper (D 6) (R 6) [6,40,80,129,33] 13 :=
  permutation_upper _ _ _ [6,40,80,65,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28847

theorem m40871_34 : Upper (D 6) (R 6) [6,40,80,129,34] 13 :=
  permutation_upper _ _ _ [6,40,80,68,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28856

theorem m40871_36 : Upper (D 6) (R 6) [6,40,80,129,36] 13 :=
  permutation_upper _ _ _ [6,40,80,66,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28852

theorem m40871_65 : Upper (D 6) (R 6) [6,40,80,129,65] 13 :=
  permutation_upper _ _ _ [6,40,80,33,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28834

theorem m40871_66 : Upper (D 6) (R 6) [6,40,80,129,66] 13 :=
  permutation_upper _ _ _ [6,40,80,36,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28841

theorem m40871_68 : Upper (D 6) (R 6) [6,40,80,129,68] 13 :=
  permutation_upper _ _ _ [6,40,80,34,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28838

theorem m40871_96 : Upper (D 6) (R 6) [6,40,80,129,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28860

def r40871 : Route 9 := (fun mask => (mask,id))

def c40871 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40871 : Upper (D 6) (R 6) [6,40,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r40871 c40871
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40871_3
  · exact m40871_5
  · exact m40871_6
  · exact m40871_33
  · exact m40871_34
  · exact m40871_36
  · exact m40871_65
  · exact m40871_66
  · exact m40871_68
  · exact m40871_96
  · exact u28864
  · exact u28865
  · exact u28866
  · exact u28867
  · exact u28868

theorem m40872_5 : Upper (D 6) (R 6) [6,40,80,130,5] 13 :=
  permutation_upper _ _ _ [6,40,80,3,132] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28822

theorem m40872_33 : Upper (D 6) (R 6) [6,40,80,130,33] 13 :=
  permutation_upper _ _ _ [6,40,80,65,132] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28849

theorem m40872_36 : Upper (D 6) (R 6) [6,40,80,130,36] 13 :=
  permutation_upper _ _ _ [6,40,80,66,132] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28853

theorem m40872_65 : Upper (D 6) (R 6) [6,40,80,130,65] 13 :=
  permutation_upper _ _ _ [6,40,80,33,132] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28836

theorem m40872_68 : Upper (D 6) (R 6) [6,40,80,130,68] 13 :=
  permutation_upper _ _ _ [6,40,80,34,132] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28839

theorem m40872_96 : Upper (D 6) (R 6) [6,40,80,130,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,132] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28862

theorem m40872_257 : Upper (D 6) (R 6) [6,40,80,130,257] 13 :=
  permutation_upper _ _ _ [6,40,80,129,260] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28866

def r40872 : Route 9 := (fun mask => (mask,id))

def c40872 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40872 : Upper (D 6) (R 6) [6,40,80,130] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r40872 c40872
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40872_5
  · exact m40872_33
  · exact m40872_36
  · exact m40872_65
  · exact m40872_68
  · exact m40872_96
  · exact m40872_257
  · exact u28869
  · exact u28870
  · exact u28871

theorem m40873_3 : Upper (D 6) (R 6) [6,40,80,132,3] 13 :=
  permutation_upper _ _ _ [6,40,80,5,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28827

theorem m40873_33 : Upper (D 6) (R 6) [6,40,80,132,33] 13 :=
  permutation_upper _ _ _ [6,40,80,65,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28848

theorem m40873_34 : Upper (D 6) (R 6) [6,40,80,132,34] 13 :=
  permutation_upper _ _ _ [6,40,80,68,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28857

theorem m40873_65 : Upper (D 6) (R 6) [6,40,80,132,65] 13 :=
  permutation_upper _ _ _ [6,40,80,33,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28835

theorem m40873_66 : Upper (D 6) (R 6) [6,40,80,132,66] 13 :=
  permutation_upper _ _ _ [6,40,80,36,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28842

theorem m40873_96 : Upper (D 6) (R 6) [6,40,80,132,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28861

theorem m40873_257 : Upper (D 6) (R 6) [6,40,80,132,257] 13 :=
  permutation_upper _ _ _ [6,40,80,129,258] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28865

def r40873 : Route 9 := (fun mask => (mask,id))

def c40873 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40873 : Upper (D 6) (R 6) [6,40,80,132] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r40873 c40873
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40873_3
  · exact m40873_33
  · exact m40873_34
  · exact m40873_65
  · exact m40873_66
  · exact m40873_96
  · exact m40873_257
  · exact u28872
  · exact u28873
  · exact u28874

def b40874 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 341, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 84 168 343 359 327 455 327), lower := (rows 7 42 84 168 16 32 64 128 256), losses := [] }

theorem u40874 : Upper (D 6) (R 6) [6,40,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40874
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40875_3 : Upper (D 6) (R 6) [6,40,80,192,3] 13 :=
  permutation_upper _ _ _ [6,40,80,5,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28828

theorem m40875_5 : Upper (D 6) (R 6) [6,40,80,192,5] 13 :=
  permutation_upper _ _ _ [6,40,80,3,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28823

theorem m40875_6 : Upper (D 6) (R 6) [6,40,80,192,6] 13 :=
  permutation_upper _ _ _ [6,40,80,6,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28832

theorem m40875_33 : Upper (D 6) (R 6) [6,40,80,192,33] 13 :=
  permutation_upper _ _ _ [6,40,80,65,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28850

theorem m40875_34 : Upper (D 6) (R 6) [6,40,80,192,34] 13 :=
  permutation_upper _ _ _ [6,40,80,68,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28858

theorem m40875_36 : Upper (D 6) (R 6) [6,40,80,192,36] 13 :=
  permutation_upper _ _ _ [6,40,80,66,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28854

theorem m40875_257 : Upper (D 6) (R 6) [6,40,80,192,257] 13 :=
  permutation_upper _ _ _ [6,40,80,129,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28867

theorem m40875_258 : Upper (D 6) (R 6) [6,40,80,192,258] 13 :=
  permutation_upper _ _ _ [6,40,80,132,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28873

theorem m40875_260 : Upper (D 6) (R 6) [6,40,80,192,260] 13 :=
  permutation_upper _ _ _ [6,40,80,130,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28870

def r40875 : Route 9 := (fun mask => (mask,id))

def c40875 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 129 => 7 | 10 => 3 | 66 => 6 | 130 => 7 | 12 => 3 | 68 => 6 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u40875 : Upper (D 6) (R 6) [6,40,80,192] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r40875 c40875
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40875_3
  · exact m40875_5
  · exact m40875_6
  · exact m40875_33
  · exact m40875_34
  · exact m40875_36
  · exact m40875_257
  · exact m40875_258
  · exact m40875_260
  · exact u28875

theorem m40876_3 : Upper (D 6) (R 6) [6,40,80,384,3] 13 :=
  permutation_upper _ _ _ [6,40,80,5,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28829

theorem m40876_5 : Upper (D 6) (R 6) [6,40,80,384,5] 13 :=
  permutation_upper _ _ _ [6,40,80,3,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28824

theorem m40876_6 : Upper (D 6) (R 6) [6,40,80,384,6] 13 :=
  permutation_upper _ _ _ [6,40,80,6,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28833

theorem m40876_33 : Upper (D 6) (R 6) [6,40,80,384,33] 13 :=
  permutation_upper _ _ _ [6,40,80,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28851

theorem m40876_34 : Upper (D 6) (R 6) [6,40,80,384,34] 13 :=
  permutation_upper _ _ _ [6,40,80,68,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28859

theorem m40876_36 : Upper (D 6) (R 6) [6,40,80,384,36] 13 :=
  permutation_upper _ _ _ [6,40,80,66,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28855

theorem m40876_65 : Upper (D 6) (R 6) [6,40,80,384,65] 13 :=
  permutation_upper _ _ _ [6,40,80,33,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28837

theorem m40876_66 : Upper (D 6) (R 6) [6,40,80,384,66] 13 :=
  permutation_upper _ _ _ [6,40,80,36,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28843

theorem m40876_68 : Upper (D 6) (R 6) [6,40,80,384,68] 13 :=
  permutation_upper _ _ _ [6,40,80,34,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28840

theorem m40876_96 : Upper (D 6) (R 6) [6,40,80,384,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28863

def r40876 : Route 9 := (fun mask => (mask,id))

def c40876 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40876 : Upper (D 6) (R 6) [6,40,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40876 c40876
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40876_3
  · exact m40876_5
  · exact m40876_6
  · exact m40876_33
  · exact m40876_34
  · exact m40876_36
  · exact m40876_65
  · exact m40876_66
  · exact m40876_68
  · exact m40876_96

def b40877 : PairBound 9 := { available := 469, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 11 469 501 469 469 469), lower := (rows 7 42 100 11 16 32 64 128 256), losses := [] }

theorem u40877 : Upper (D 6) (R 6) [6,40,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40877
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40878 : PairBound 9 := { available := 467, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 13 467 499 467 467 467), lower := (rows 7 42 100 13 16 32 64 128 256), losses := [] }

theorem u40878 : Upper (D 6) (R 6) [6,40,96,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40878
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40879 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 14 465 497 465 465 465), lower := (rows 7 42 100 14 16 32 64 128 256), losses := [] }

theorem u40879 : Upper (D 6) (R 6) [6,40,96,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40879
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40880 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40880 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u40880 : Upper (D 6) (R 6) [6,40,96,17] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r40880 c40880
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28876
  · exact u28877
  · exact u28878
  · exact u28879
  · exact u28880
  · exact u28881
  · exact u28882
  · exact u28883
  · exact u28884
  · exact u28885
  · exact u28886

def b40881 : PairBound 9 := { available := 453, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 100 26 469 485 453 453 453), lower := (rows 7 42 100 26 16 32 64 128 256), losses := [] }

theorem u40881 : Upper (D 6) (R 6) [6,40,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40881
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40882 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 464, targets := 4 }], pairs := [(3,5),(4,2),(4,5)], upper := (rows 7 42 100 28 467 483 451 451 451), lower := (rows 7 42 100 28 16 32 64 128 256), losses := [] }

theorem u40882 : Upper (D 6) (R 6) [6,40,96,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40882
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40883 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 7 42 100 73 407 439 471 407 407), lower := (rows 7 42 100 73 16 32 64 128 256), losses := [] }

theorem u40883 : Upper (D 6) (R 6) [6,40,96,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40883
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40884 : PairBound 9 := { available := 405, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 100 74 405 437 469 405 405), lower := (rows 7 42 100 74 16 32 64 128 256), losses := [] }

theorem u40884 : Upper (D 6) (R 6) [6,40,96,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40884
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40885 : PairBound 9 := { available := 403, camps := [{ cop := 3, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 42 100 76 403 435 467 403 403), lower := (rows 7 42 100 76 16 32 64 128 256), losses := [] }

theorem u40885 : Upper (D 6) (R 6) [6,40,96,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40885
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40886 : PairBound 9 := { available := 391, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 7 42 100 88 407 423 455 391 391), lower := (rows 7 42 100 88 16 32 64 128 256), losses := [] }

theorem u40886 : Upper (D 6) (R 6) [6,40,96,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40886
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40887 : Route 9 := (fun mask => (mask,id))

def c40887 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40887 : Upper (D 6) (R 6) [6,40,96,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40887 c40887
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28887
  · exact u28888
  · exact u28889
  · exact u28890
  · exact u28891
  · exact u28892
  · exact u28893
  · exact u28894
  · exact u28895
  · exact u28896

def b40888 : PairBound 9 := { available := 341, camps := [{ cop := 0, region := 372, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 100 138 341 373 341 469 341), lower := (rows 7 42 100 138 16 32 64 128 256), losses := [] }

theorem u40888 : Upper (D 6) (R 6) [6,40,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40888
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40889 : PairBound 9 := { available := 339, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 336, targets := 4 }], pairs := [(3,5),(4,2),(4,5)], upper := (rows 7 42 100 140 339 371 339 467 339), lower := (rows 7 42 100 140 16 32 64 128 256), losses := [] }

theorem u40889 : Upper (D 6) (R 6) [6,40,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40889
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40890 : Route 9 := (fun mask => (mask,id))

def c40890 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40890 : Upper (D 6) (R 6) [6,40,96,144] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40890 c40890
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28897
  · exact u28898
  · exact u28899
  · exact u28900
  · exact u28901
  · exact u28902
  · exact u28903
  · exact u28904
  · exact u28905
  · exact u28906

def b40891 : PairBound 9 := { available := 279, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 272, targets := 64 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 7 42 100 200 279 311 343 407 279), lower := (rows 7 42 100 200 16 32 64 128 256), losses := [] }

theorem u40891 : Upper (D 6) (R 6) [6,40,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40891
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40892 : Route 9 := (fun mask => (mask,id))

def c40892 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40892 : Upper (D 6) (R 6) [6,40,96,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384] 13 (by decide) (choices 2) [3,5,6,65,66,68] r40892 c40892
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28907
  · exact u28908
  · exact u28909
  · exact u28910
  · exact u28911
  · exact u28912

def b40893 : PairBound 9 := { available := 372, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 42 133 11 372 372 372 500 372), lower := (rows 7 42 133 11 16 32 64 128 256), losses := [] }

theorem u40893 : Upper (D 6) (R 6) [6,40,129,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40893
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40894 : PairBound 9 := { available := 370, camps := [{ cop := 3, region := 370, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 42 133 13 370 370 370 498 370), lower := (rows 7 42 133 13 16 32 64 128 256), losses := [] }

theorem u40894 : Upper (D 6) (R 6) [6,40,129,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40894
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40895 : PairBound 9 := { available := 369, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 133 14 369 369 369 497 369), lower := (rows 7 42 133 14 16 32 64 128 256), losses := [] }

theorem u40895 : Upper (D 6) (R 6) [6,40,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40895
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40896 : Route 9 := (fun mask => (mask,id))

def c40896 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40896 : Upper (D 6) (R 6) [6,40,129,17] 13 := by
  apply FastRouting.sound _ _ [6,40,129,17] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r40896 c40896
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28913
  · exact u28914
  · exact u28915
  · exact u28916
  · exact u28917
  · exact u28918
  · exact u28919
  · exact u28920
  · exact u28921
  · exact u28922

def r40897 : Route 9 := (fun mask => (mask,id))

def c40897 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40897 : Upper (D 6) (R 6) [6,40,129,18] 13 := by
  apply FastRouting.sound _ _ [6,40,129,18] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r40897 c40897
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28923
  · exact u28924
  · exact u28925
  · exact u28926
  · exact u28927
  · exact u28928
  · exact u28929
  · exact u28930
  · exact u28931
  · exact u28932

def r40898 : Route 9 := (fun mask => (mask,id))

def c40898 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40898 : Upper (D 6) (R 6) [6,40,129,20] 13 := by
  apply FastRouting.sound _ _ [6,40,129,20] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r40898 c40898
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28933
  · exact u28934
  · exact u28935
  · exact u28936
  · exact u28937
  · exact u28938
  · exact u28939
  · exact u28940
  · exact u28941
  · exact u28942

def b40899 : PairBound 9 := { available := 342, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 133 41 342 374 342 470 342), lower := (rows 7 42 133 41 16 32 64 128 256), losses := [] }

theorem u40899 : Upper (D 6) (R 6) [6,40,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40899
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40900 : PairBound 9 := { available := 341, camps := [{ cop := 5, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 42 341 373 341 469 341), lower := (rows 7 42 133 42 16 32 64 128 256), losses := [] }

theorem u40900 : Upper (D 6) (R 6) [6,40,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40900
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40901 : PairBound 9 := { available := 339, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 133 44 339 371 339 467 339), lower := (rows 7 42 133 44 16 32 64 128 256), losses := [] }

theorem u40901 : Upper (D 6) (R 6) [6,40,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40901
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40902 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 133 56 343 359 327 455 327), lower := (rows 7 42 133 56 16 32 64 128 256), losses := [] }

theorem u40902 : Upper (D 6) (R 6) [6,40,129,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40902
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40903 : Route 9 := (fun mask => (mask,id))

def c40903 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40903 : Upper (D 6) (R 6) [6,40,129,65] 13 := by
  apply FastRouting.sound _ _ [6,40,129,65] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r40903 c40903
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28943
  · exact u28944
  · exact u28945
  · exact u28946
  · exact u28947
  · exact u28948
  · exact u28949
  · exact u28950
  · exact u28951
  · exact u28952

def r40904 : Route 9 := (fun mask => (mask,id))

def c40904 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40904 : Upper (D 6) (R 6) [6,40,129,66] 13 := by
  apply FastRouting.sound _ _ [6,40,129,66] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r40904 c40904
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28953
  · exact u28954
  · exact u28955
  · exact u28956
  · exact u28957
  · exact u28958
  · exact u28959
  · exact u28960
  · exact u28961
  · exact u28962

def r40905 : Route 9 := (fun mask => (mask,id))

def c40905 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40905 : Upper (D 6) (R 6) [6,40,129,68] 13 := by
  apply FastRouting.sound _ _ [6,40,129,68] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r40905 c40905
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28963
  · exact u28964
  · exact u28965
  · exact u28966
  · exact u28967
  · exact u28968
  · exact u28969
  · exact u28970
  · exact u28971
  · exact u28972

def r40906 : Route 9 := (fun mask => (mask,id))

def c40906 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40906 : Upper (D 6) (R 6) [6,40,129,80] 13 := by
  apply FastRouting.sound _ _ [6,40,129,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r40906 c40906
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28973
  · exact u28974
  · exact u28975
  · exact u28976
  · exact u28977
  · exact u28978
  · exact u28979
  · exact u28980
  · exact u28981
  · exact u28982
  · exact u28983
  · exact u28984
  · exact u28985
  · exact u28986
  · exact u28987

def b40907 : PairBound 9 := { available := 343, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 133 104 343 375 343 471 343), lower := (rows 7 42 133 104 16 32 64 128 256), losses := [] }

theorem u40907 : Upper (D 6) (R 6) [6,40,129,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40907
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40908 : Route 9 := (fun mask => (mask,id))

def c40908 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40908 : Upper (D 6) (R 6) [6,40,129,257] 13 := by
  apply FastRouting.sound _ _ [6,40,129,257] 13 (by decide) (choices 2) [6,34,36,66,68,96] r40908 c40908
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28988
  · exact u28989
  · exact u28990
  · exact u28991
  · exact u28992
  · exact u28993

def r40909 : Route 9 := (fun mask => (mask,id))

def c40909 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40909 : Upper (D 6) (R 6) [6,40,129,258] 13 := by
  apply FastRouting.sound _ _ [6,40,129,258] 13 (by decide) (choices 2) [5,33,36,65,68,96] r40909 c40909
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28994
  · exact u28995
  · exact u28996
  · exact u28997
  · exact u28998
  · exact u28999

def r40910 : Route 9 := (fun mask => (mask,id))

def c40910 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40910 : Upper (D 6) (R 6) [6,40,129,260] 13 := by
  apply FastRouting.sound _ _ [6,40,129,260] 13 (by decide) (choices 2) [3,33,34,65,66,96] r40910 c40910
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29000
  · exact u29001
  · exact u29002
  · exact u29003
  · exact u29004
  · exact u29005

def r40911 : Route 9 := (fun mask => (mask,id))

def c40911 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40911 : Upper (D 6) (R 6) [6,40,129,272] 13 := by
  apply FastRouting.sound _ _ [6,40,129,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40911 c40911
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29006
  · exact u29007
  · exact u29008
  · exact u29009
  · exact u29010
  · exact u29011
  · exact u29012
  · exact u29013
  · exact u29014
  · exact u29015

def b40912 : PairBound 9 := { available := 87, camps := [{ cop := 1, region := 213, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 133 296 87 119 87 215 343), lower := (rows 7 42 133 296 16 32 64 128 256), losses := [] }

theorem u40912 : Upper (D 6) (R 6) [6,40,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40912
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40913 : Route 9 := (fun mask => (mask,id))

def c40913 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40913 : Upper (D 6) (R 6) [6,40,129,320] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40913 c40913
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u29016
  · exact u29017
  · exact u29018
  · exact u29019
  · exact u29020
  · exact u29021
  · exact u29022
  · exact u29023
  · exact u29024
  · exact u29025

def b40914 : PairBound 9 := { available := 357, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 42 148 11 373 357 357 485 357), lower := (rows 7 42 148 11 16 32 64 128 256), losses := [] }

theorem u40914 : Upper (D 6) (R 6) [6,40,144,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40914
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40915 : PairBound 9 := { available := 355, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 42 148 13 371 355 355 483 355), lower := (rows 7 42 148 13 16 32 64 128 256), losses := [] }

theorem u40915 : Upper (D 6) (R 6) [6,40,144,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40915
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40916 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 148 14 369 353 353 481 353), lower := (rows 7 42 148 14 16 32 64 128 256), losses := [] }

theorem u40916 : Upper (D 6) (R 6) [6,40,144,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40916
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40917 : PairBound 9 := { available := 327, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 148 41 343 359 327 455 327), lower := (rows 7 42 148 41 16 32 64 128 256), losses := [] }

theorem u40917 : Upper (D 6) (R 6) [6,40,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40917
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40918 : PairBound 9 := { available := 325, camps := [{ cop := 5, region := 10, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 148 42 341 357 325 453 325), lower := (rows 7 42 148 42 16 32 64 128 256), losses := [] }

theorem u40918 : Upper (D 6) (R 6) [6,40,144,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40918
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40919 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 42 148 44 339 355 323 451 323), lower := (rows 7 42 148 44 16 32 64 128 256), losses := [] }

theorem u40919 : Upper (D 6) (R 6) [6,40,144,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40919
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u40919
end Delivery.IrregularNine14.P06
