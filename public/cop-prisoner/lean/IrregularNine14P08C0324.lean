import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0147
import IrregularNine14P08C0148
import IrregularNine14P08C0149
import IrregularNine14P08C0150
import IrregularNine14P08C0151
import IrregularNine14P08C0152

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19440 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 200 433 417 481 417 417), lower := (rows 35 70 28 200 16 32 64 128 256), losses := [] }

theorem u19440 : Upper (D 8) (R 8) [34,68,24,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19441_33 : Upper (D 8) (R 8) [34,68,24,257,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8879

theorem m19441_65 : Upper (D 8) (R 8) [34,68,24,257,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8884

theorem m19441_96 : Upper (D 8) (R 8) [34,68,24,257,96] 13 :=
  permutation_upper _ _ _ [34,68,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8889

theorem m19441_129 : Upper (D 8) (R 8) [34,68,24,257,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8895

theorem m19441_160 : Upper (D 8) (R 8) [34,68,24,257,160] 13 :=
  permutation_upper _ _ _ [34,68,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8901

theorem m19441_192 : Upper (D 8) (R 8) [34,68,24,257,192] 13 :=
  permutation_upper _ _ _ [34,68,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8905

def r19441 : Route 9 := (fun mask => (mask,id))

def c19441 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19441 : Upper (D 8) (R 8) [34,68,24,257] 13 := by
  apply FastRouting.sound _ _ [34,68,24,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19441 c19441
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19441_33
  · exact m19441_65
  · exact m19441_96
  · exact m19441_129
  · exact m19441_160
  · exact m19441_192

theorem m19442_33 : Upper (D 8) (R 8) [34,68,24,288,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8880

theorem m19442_65 : Upper (D 8) (R 8) [34,68,24,288,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8885

theorem m19442_96 : Upper (D 8) (R 8) [34,68,24,288,96] 13 :=
  permutation_upper _ _ _ [34,68,24,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8890

theorem m19442_129 : Upper (D 8) (R 8) [34,68,24,288,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8896

theorem m19442_160 : Upper (D 8) (R 8) [34,68,24,288,160] 13 :=
  permutation_upper _ _ _ [34,68,24,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8902

theorem m19442_192 : Upper (D 8) (R 8) [34,68,24,288,192] 13 :=
  permutation_upper _ _ _ [34,68,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8906

def r19442 : Route 9 := (fun mask => (mask,id))

def c19442 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19442 : Upper (D 8) (R 8) [34,68,24,288] 13 := by
  apply FastRouting.sound _ _ [34,68,24,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19442 c19442
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19442_33
  · exact m19442_65
  · exact m19442_96
  · exact m19442_129
  · exact m19442_160
  · exact m19442_192

def b19443 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 328 177 161 225 161 417), lower := (rows 35 70 28 328 16 32 64 128 256), losses := [] }

theorem u19443 : Upper (D 8) (R 8) [34,68,24,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19444_33 : Upper (D 8) (R 8) [34,68,24,384,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8881

theorem m19444_65 : Upper (D 8) (R 8) [34,68,24,384,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8886

theorem m19444_96 : Upper (D 8) (R 8) [34,68,24,384,96] 13 :=
  permutation_upper _ _ _ [34,68,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8891

theorem m19444_129 : Upper (D 8) (R 8) [34,68,24,384,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8898

theorem m19444_160 : Upper (D 8) (R 8) [34,68,24,384,160] 13 :=
  permutation_upper _ _ _ [34,68,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8904

theorem m19444_192 : Upper (D 8) (R 8) [34,68,24,384,192] 13 :=
  permutation_upper _ _ _ [34,68,24,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8907

def r19444 : Route 9 := (fun mask => (mask,id))

def c19444 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19444 : Upper (D 8) (R 8) [34,68,24,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19444 c19444
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19444_33
  · exact m19444_65
  · exact m19444_96
  · exact m19444_129
  · exact m19444_160
  · exact m19444_192

def r19445 : Route 9 := (fun mask => (mask,id))

def c19445 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19445 : Upper (D 8) (R 8) [34,68,40,17] 13 := by
  apply FastRouting.sound _ _ [34,68,40,17] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19445 c19445
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8908
  · exact u8909
  · exact u8910
  · exact u8911
  · exact u8912
  · exact u8913
  · exact u8914
  · exact u8915
  · exact u8916
  · exact u8917

def b19446 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 41 465 497 465 465 465), lower := (rows 35 70 44 41 16 32 64 128 256), losses := [] }

theorem u19446 : Upper (D 8) (R 8) [34,68,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19447 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 70 44 56 465 481 449 449 449), lower := (rows 35 70 44 56 16 32 64 128 256), losses := [] }

theorem u19447 : Upper (D 8) (R 8) [34,68,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19448 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 73 433 433 497 433 433), lower := (rows 35 70 44 73 16 32 64 128 256), losses := [] }

theorem u19448 : Upper (D 8) (R 8) [34,68,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19449 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 88 433 417 481 417 417), lower := (rows 35 70 44 88 16 32 64 128 256), losses := [] }

theorem u19449 : Upper (D 8) (R 8) [34,68,40,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19450 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 104 401 433 465 401 401), lower := (rows 35 70 44 104 16 32 64 128 256), losses := [] }

theorem u19450 : Upper (D 8) (R 8) [34,68,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19451 : Route 9 := (fun mask => (mask,id))

def c19451 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19451 : Upper (D 8) (R 8) [34,68,40,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19451 c19451
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8918
  · exact u8919
  · exact u8920
  · exact u8921
  · exact u8922
  · exact u8923
  · exact u8924
  · exact u8925
  · exact u8926
  · exact u8927

def r19452 : Route 9 := (fun mask => (mask,id))

def c19452 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19452 : Upper (D 8) (R 8) [34,68,40,144] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19452 c19452
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8928
  · exact u8929
  · exact u8930
  · exact u8931
  · exact u8932
  · exact u8933
  · exact u8934
  · exact u8935
  · exact u8936
  · exact u8937

def b19453 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 70 44 168 465 497 465 465 465), lower := (rows 35 70 44 168 16 32 64 128 256), losses := [] }

theorem u19453 : Upper (D 8) (R 8) [34,68,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19454 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 200 433 433 497 433 433), lower := (rows 35 70 44 200 16 32 64 128 256), losses := [] }

theorem u19454 : Upper (D 8) (R 8) [34,68,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19455 : Route 9 := (fun mask => (mask,id))

def c19455 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19455 : Upper (D 8) (R 8) [34,68,40,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19455 c19455
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8938
  · exact u8939
  · exact u8940
  · exact u8941
  · exact u8942
  · exact u8943

def r19456 : Route 9 := (fun mask => (mask,id))

def c19456 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19456 : Upper (D 8) (R 8) [34,68,40,272] 13 := by
  apply FastRouting.sound _ _ [34,68,40,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19456 c19456
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8944
  · exact u8945
  · exact u8946
  · exact u8947
  · exact u8948
  · exact u8949

def b19457 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 35 70 44 296 209 241 209 209 465), lower := (rows 35 70 44 296 16 32 64 128 256), losses := [] }

theorem u19457 : Upper (D 8) (R 8) [34,68,40,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19458 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 328 177 177 241 177 433), lower := (rows 35 70 44 328 16 32 64 128 256), losses := [] }

theorem u19458 : Upper (D 8) (R 8) [34,68,40,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19459 : Route 9 := (fun mask => (mask,id))

def c19459 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19459 : Upper (D 8) (R 8) [34,68,40,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19459 c19459
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8950
  · exact u8951
  · exact u8952
  · exact u8953
  · exact u8954
  · exact u8955

def b19460 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 133 25 504 488 488 488 488), lower := (rows 35 70 133 25 16 32 64 128 256), losses := [] }

theorem u19460 : Upper (D 8) (R 8) [34,68,129,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19461 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 41 504 504 504 504 504), lower := (rows 35 70 133 41 16 32 64 128 256), losses := [] }

theorem u19461 : Upper (D 8) (R 8) [34,68,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19462_9 : Upper (D 8) (R 8) [34,68,129,48,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8956

theorem m19462_33 : Upper (D 8) (R 8) [34,68,129,48,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8966

def r19462 : Route 9 := (fun mask => (mask,id))

def c19462 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u19462 : Upper (D 8) (R 8) [34,68,129,48] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r19462 c19462
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19462_9
  · exact m19462_33
  · exact u8976
  · exact u8977
  · exact u8978
  · exact u8979
  · exact u8980
  · exact u8981
  · exact u8982
  · exact u8983
  · exact u8984
  · exact u8985
  · exact u8986
  · exact u8987
  · exact u8988

def b19463 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 440 440 504 440 440), lower := (rows 35 70 133 73 16 32 64 128 256), losses := [] }

theorem u19463 : Upper (D 8) (R 8) [34,68,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19464_9 : Upper (D 8) (R 8) [34,68,129,80,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8957

theorem m19464_33 : Upper (D 8) (R 8) [34,68,129,80,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8967

theorem m19464_40 : Upper (D 8) (R 8) [34,68,129,80,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8978

def r19464 : Route 9 := (fun mask => (mask,id))

def c19464 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u19464 : Upper (D 8) (R 8) [34,68,129,80] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r19464 c19464
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19464_9
  · exact m19464_33
  · exact m19464_40
  · exact u8994
  · exact u8995
  · exact u8996
  · exact u8997
  · exact u8998
  · exact u8999
  · exact u9000

theorem m19465_9 : Upper (D 8) (R 8) [34,68,129,96,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8958

theorem m19465_33 : Upper (D 8) (R 8) [34,68,129,96,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8968

theorem m19465_40 : Upper (D 8) (R 8) [34,68,129,96,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8979

def r19465 : Route 9 := (fun mask => (mask,id))

def c19465 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u19465 : Upper (D 8) (R 8) [34,68,129,96] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r19465 c19465
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19465_9
  · exact m19465_33
  · exact m19465_40
  · exact u9001
  · exact u9002
  · exact u9003
  · exact u9004
  · exact u9005
  · exact u9006
  · exact u9007

def b19466 : PairBound 9 := { available := 376, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 137 376 376 376 504 376), lower := (rows 35 70 133 137 16 32 64 128 256), losses := [] }

theorem u19466 : Upper (D 8) (R 8) [34,68,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19467_9 : Upper (D 8) (R 8) [34,68,129,144,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8959

theorem m19467_33 : Upper (D 8) (R 8) [34,68,129,144,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8969

theorem m19467_40 : Upper (D 8) (R 8) [34,68,129,144,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8981

theorem m19467_65 : Upper (D 8) (R 8) [34,68,129,144,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8989

theorem m19467_72 : Upper (D 8) (R 8) [34,68,129,144,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8995

theorem m19467_96 : Upper (D 8) (R 8) [34,68,129,144,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9002

def r19467 : Route 9 := (fun mask => (mask,id))

def c19467 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u19467 : Upper (D 8) (R 8) [34,68,129,144] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r19467 c19467
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19467_9
  · exact m19467_33
  · exact m19467_40
  · exact m19467_65
  · exact m19467_72
  · exact m19467_96
  · exact u9011
  · exact u9012
  · exact u9013
  · exact u9014

theorem m19468_9 : Upper (D 8) (R 8) [34,68,129,160,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8960

theorem m19468_33 : Upper (D 8) (R 8) [34,68,129,160,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8970

theorem m19468_40 : Upper (D 8) (R 8) [34,68,129,160,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8982

theorem m19468_65 : Upper (D 8) (R 8) [34,68,129,160,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8990

theorem m19468_72 : Upper (D 8) (R 8) [34,68,129,160,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8996

theorem m19468_96 : Upper (D 8) (R 8) [34,68,129,160,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9003

def r19468 : Route 9 := (fun mask => (mask,id))

def c19468 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u19468 : Upper (D 8) (R 8) [34,68,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r19468 c19468
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19468_9
  · exact m19468_33
  · exact m19468_40
  · exact m19468_65
  · exact m19468_72
  · exact m19468_96
  · exact u9015
  · exact u9016
  · exact u9017
  · exact u9018

theorem m19469_9 : Upper (D 8) (R 8) [34,68,129,192,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8961

theorem m19469_33 : Upper (D 8) (R 8) [34,68,129,192,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8971

theorem m19469_40 : Upper (D 8) (R 8) [34,68,129,192,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8983

def r19469 : Route 9 := (fun mask => (mask,id))

def c19469 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u19469 : Upper (D 8) (R 8) [34,68,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r19469 c19469
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19469_9
  · exact m19469_33
  · exact m19469_40
  · exact u9019
  · exact u9020
  · exact u9021

def b19470 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 133 265 248 248 248 248 504), lower := (rows 35 70 133 265 16 32 64 128 256), losses := [] }

theorem u19470 : Upper (D 8) (R 8) [34,68,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19471_9 : Upper (D 8) (R 8) [34,68,129,272,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8962

theorem m19471_33 : Upper (D 8) (R 8) [34,68,129,272,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8972

theorem m19471_40 : Upper (D 8) (R 8) [34,68,129,272,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8985

theorem m19471_65 : Upper (D 8) (R 8) [34,68,129,272,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8991

theorem m19471_72 : Upper (D 8) (R 8) [34,68,129,272,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8998

theorem m19471_96 : Upper (D 8) (R 8) [34,68,129,272,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9005

theorem m19471_129 : Upper (D 8) (R 8) [34,68,129,272,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9008

theorem m19471_136 : Upper (D 8) (R 8) [34,68,129,272,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9012

theorem m19471_160 : Upper (D 8) (R 8) [34,68,129,272,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9016

theorem m19471_192 : Upper (D 8) (R 8) [34,68,129,272,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9020

def r19471 : Route 9 := (fun mask => (mask,id))

def c19471 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19471 : Upper (D 8) (R 8) [34,68,129,272] 13 := by
  apply FastRouting.sound _ _ [34,68,129,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19471 c19471
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19471_9
  · exact m19471_33
  · exact m19471_40
  · exact m19471_65
  · exact m19471_72
  · exact m19471_96
  · exact m19471_129
  · exact m19471_136
  · exact m19471_160
  · exact m19471_192

theorem m19472_9 : Upper (D 8) (R 8) [34,68,129,288,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8963

theorem m19472_33 : Upper (D 8) (R 8) [34,68,129,288,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8973

theorem m19472_40 : Upper (D 8) (R 8) [34,68,129,288,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8986

theorem m19472_65 : Upper (D 8) (R 8) [34,68,129,288,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8992

theorem m19472_72 : Upper (D 8) (R 8) [34,68,129,288,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8999

theorem m19472_96 : Upper (D 8) (R 8) [34,68,129,288,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9006

theorem m19472_129 : Upper (D 8) (R 8) [34,68,129,288,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9009

theorem m19472_136 : Upper (D 8) (R 8) [34,68,129,288,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9013

theorem m19472_160 : Upper (D 8) (R 8) [34,68,129,288,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9017

theorem m19472_192 : Upper (D 8) (R 8) [34,68,129,288,192] 13 :=
  permutation_upper _ _ _ [34,68,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9021

def r19472 : Route 9 := (fun mask => (mask,id))

def c19472 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19472 : Upper (D 8) (R 8) [34,68,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r19472 c19472
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19472_9
  · exact m19472_33
  · exact m19472_40
  · exact m19472_65
  · exact m19472_72
  · exact m19472_96
  · exact m19472_129
  · exact m19472_136
  · exact m19472_160
  · exact m19472_192

theorem m19473_9 : Upper (D 8) (R 8) [34,68,129,320,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8964

theorem m19473_33 : Upper (D 8) (R 8) [34,68,129,320,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8974

theorem m19473_40 : Upper (D 8) (R 8) [34,68,129,320,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8987

theorem m19473_129 : Upper (D 8) (R 8) [34,68,129,320,129] 13 :=
  permutation_upper _ _ _ [34,68,129,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9010

theorem m19473_136 : Upper (D 8) (R 8) [34,68,129,320,136] 13 :=
  permutation_upper _ _ _ [34,68,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9014

theorem m19473_160 : Upper (D 8) (R 8) [34,68,129,320,160] 13 :=
  permutation_upper _ _ _ [34,68,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9018

def r19473 : Route 9 := (fun mask => (mask,id))

def c19473 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u19473 : Upper (D 8) (R 8) [34,68,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r19473 c19473
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19473_9
  · exact m19473_33
  · exact m19473_40
  · exact m19473_129
  · exact m19473_136
  · exact m19473_160

theorem m19474_9 : Upper (D 8) (R 8) [34,68,129,384,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8965

theorem m19474_33 : Upper (D 8) (R 8) [34,68,129,384,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8975

theorem m19474_40 : Upper (D 8) (R 8) [34,68,129,384,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8988

theorem m19474_65 : Upper (D 8) (R 8) [34,68,129,384,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8993

theorem m19474_72 : Upper (D 8) (R 8) [34,68,129,384,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9000

theorem m19474_96 : Upper (D 8) (R 8) [34,68,129,384,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9007

def r19474 : Route 9 := (fun mask => (mask,id))

def c19474 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u19474 : Upper (D 8) (R 8) [34,68,129,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,384] 13 (by decide) (choices 2) [9,33,40,65,72,96] r19474 c19474
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19474_9
  · exact m19474_33
  · exact m19474_40
  · exact m19474_65
  · exact m19474_72
  · exact m19474_96

def r19475 : Route 9 := (fun mask => (mask,id))

def c19475 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19475 : Upper (D 8) (R 8) [34,68,136,17] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19475 c19475
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9022
  · exact u9023
  · exact u9024
  · exact u9025
  · exact u9026
  · exact u9027
  · exact u9028
  · exact u9029
  · exact u9030
  · exact u9031

def b19476 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 140 41 497 497 497 497 497), lower := (rows 35 70 140 41 16 32 64 128 256), losses := [] }

theorem u19476 : Upper (D 8) (R 8) [34,68,136,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19477 : Route 9 := (fun mask => (mask,id))

def c19477 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u19477 : Upper (D 8) (R 8) [34,68,136,48] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r19477 c19477
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9032
  · exact u9033
  · exact u9034
  · exact u9035
  · exact u9036
  · exact u9037
  · exact u9038
  · exact u9039
  · exact u9040
  · exact u9041

def b19478 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 73 433 433 497 433 433), lower := (rows 35 70 140 73 16 32 64 128 256), losses := [] }

theorem u19478 : Upper (D 8) (R 8) [34,68,136,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19479 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 88 433 417 481 417 417), lower := (rows 35 70 140 88 16 32 64 128 256), losses := [] }

theorem u19479 : Upper (D 8) (R 8) [34,68,136,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19480 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 104 433 433 497 433 433), lower := (rows 35 70 140 104 16 32 64 128 256), losses := [] }

theorem u19480 : Upper (D 8) (R 8) [34,68,136,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19481 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 137 369 369 369 497 369), lower := (rows 35 70 140 137 16 32 64 128 256), losses := [] }

theorem u19481 : Upper (D 8) (R 8) [34,68,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19482 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 152 369 353 353 481 353), lower := (rows 35 70 140 152 16 32 64 128 256), losses := [] }

theorem u19482 : Upper (D 8) (R 8) [34,68,136,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19483 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 168 369 369 369 497 369), lower := (rows 35 70 140 168 16 32 64 128 256), losses := [] }

theorem u19483 : Upper (D 8) (R 8) [34,68,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19484 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 140 200 305 305 369 433 305), lower := (rows 35 70 140 200 16 32 64 128 256), losses := [] }

theorem u19484 : Upper (D 8) (R 8) [34,68,136,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19485 : Route 9 := (fun mask => (mask,id))

def c19485 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19485 : Upper (D 8) (R 8) [34,68,136,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19485 c19485
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9042
  · exact u9043
  · exact u9044
  · exact u9045
  · exact u9046
  · exact u9047

def r19486 : Route 9 := (fun mask => (mask,id))

def c19486 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19486 : Upper (D 8) (R 8) [34,68,136,272] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19486 c19486
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9048
  · exact u9049
  · exact u9050
  · exact u9051
  · exact u9052
  · exact u9053

def r19487 : Route 9 := (fun mask => (mask,id))

def c19487 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u19487 : Upper (D 8) (R 8) [34,68,136,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r19487 c19487
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9054
  · exact u9055
  · exact u9056
  · exact u9057
  · exact u9058
  · exact u9059

def b19488 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 328 177 177 241 177 433), lower := (rows 35 70 140 328 16 32 64 128 256), losses := [] }

theorem u19488 : Upper (D 8) (R 8) [34,68,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19489 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 392 113 113 113 241 369), lower := (rows 35 70 140 392 16 32 64 128 256), losses := [] }

theorem u19489 : Upper (D 8) (R 8) [34,68,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r19490 : Route 9 := (fun mask => (mask,id))

def c19490 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u19490 : Upper (D 8) (R 8) [34,68,160,17] 13 := by
  apply FastRouting.sound _ _ [34,68,160,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r19490 c19490
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9060
  · exact u9061
  · exact u9062
  · exact u9063
  · exact u9064
  · exact u9065
  · exact u9066
  · exact u9067
  · exact u9068
  · exact u9069
  · exact u9070
  · exact u9071
  · exact u9072
  · exact u9073
  · exact u9074

def b19491 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 164 41 473 505 473 473 473), lower := (rows 35 70 164 41 16 32 64 128 256), losses := [] }

theorem u19491 : Upper (D 8) (R 8) [34,68,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19492_9 : Upper (D 8) (R 8) [34,68,160,48,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9062

def r19492 : Route 9 := (fun mask => (mask,id))

def c19492 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u19492 : Upper (D 8) (R 8) [34,68,160,48] 13 := by
  apply FastRouting.sound _ _ [34,68,160,48] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r19492 c19492
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19492_9
  · exact u9082
  · exact u9083
  · exact u9084
  · exact u9085
  · exact u9086
  · exact u9087
  · exact u9088
  · exact u9089
  · exact u9090

def b19493 : PairBound 9 := { available := 441, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 73 441 441 505 441 441), lower := (rows 35 70 164 73 16 32 64 128 256), losses := [] }

theorem u19493 : Upper (D 8) (R 8) [34,68,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19494_9 : Upper (D 8) (R 8) [34,68,160,80,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9064

theorem m19494_33 : Upper (D 8) (R 8) [34,68,160,80,33] 13 :=
  permutation_upper _ _ _ [34,68,160,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9075

theorem m19494_40 : Upper (D 8) (R 8) [34,68,160,80,40] 13 :=
  permutation_upper _ _ _ [34,68,160,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9083

def r19494 : Route 9 := (fun mask => (mask,id))

def c19494 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u19494 : Upper (D 8) (R 8) [34,68,160,80] 13 := by
  apply FastRouting.sound _ _ [34,68,160,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r19494 c19494
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19494_9
  · exact m19494_33
  · exact m19494_40
  · exact u9096
  · exact u9097
  · exact u9098
  · exact u9099
  · exact u9100
  · exact u9101
  · exact u9102

theorem m19495_9 : Upper (D 8) (R 8) [34,68,160,96,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9065

def r19495 : Route 9 := (fun mask => (mask,id))

def c19495 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u19495 : Upper (D 8) (R 8) [34,68,160,96] 13 := by
  apply FastRouting.sound _ _ [34,68,160,96] 13 (by decide) (choices 2) [9,129,136,257,264,384] r19495 c19495
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19495_9
  · exact u9103
  · exact u9104
  · exact u9105
  · exact u9106
  · exact u9107

def b19496 : PairBound 9 := { available := 377, camps := [{ cop := 3, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 164 137 377 377 377 505 377), lower := (rows 35 70 164 137 16 32 64 128 256), losses := [] }

theorem u19496 : Upper (D 8) (R 8) [34,68,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19497_9 : Upper (D 8) (R 8) [34,68,160,144,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9067

theorem m19497_33 : Upper (D 8) (R 8) [34,68,160,144,33] 13 :=
  permutation_upper _ _ _ [34,68,160,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9076

theorem m19497_40 : Upper (D 8) (R 8) [34,68,160,144,40] 13 :=
  permutation_upper _ _ _ [34,68,160,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9085

theorem m19497_65 : Upper (D 8) (R 8) [34,68,160,144,65] 13 :=
  permutation_upper _ _ _ [34,68,160,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9091

theorem m19497_72 : Upper (D 8) (R 8) [34,68,160,144,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9097

theorem m19497_96 : Upper (D 8) (R 8) [34,68,160,144,96] 13 :=
  permutation_upper _ _ _ [34,68,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9104

def r19497 : Route 9 := (fun mask => (mask,id))

def c19497 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u19497 : Upper (D 8) (R 8) [34,68,160,144] 13 := by
  apply FastRouting.sound _ _ [34,68,160,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r19497 c19497
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19497_9
  · exact m19497_33
  · exact m19497_40
  · exact m19497_65
  · exact m19497_72
  · exact m19497_96
  · exact u9112
  · exact u9113
  · exact u9114
  · exact u9115

def b19498 : PairBound 9 := { available := 345, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 164 168 345 377 345 473 345), lower := (rows 35 70 164 168 16 32 64 128 256), losses := [] }

theorem u19498 : Upper (D 8) (R 8) [34,68,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m19499_9 : Upper (D 8) (R 8) [34,68,160,192,9] 13 :=
  permutation_upper _ _ _ [34,68,160,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9069

theorem m19499_33 : Upper (D 8) (R 8) [34,68,160,192,33] 13 :=
  permutation_upper _ _ _ [34,68,160,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9077

theorem m19499_40 : Upper (D 8) (R 8) [34,68,160,192,40] 13 :=
  permutation_upper _ _ _ [34,68,160,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9086

def r19499 : Route 9 := (fun mask => (mask,id))

def c19499 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u19499 : Upper (D 8) (R 8) [34,68,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192] 13 (by decide) (choices 2) [9,33,40,257,264,288] r19499 c19499
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m19499_9
  · exact m19499_33
  · exact m19499_40
  · exact u9119
  · exact u9120
  · exact u9121

#print axioms u19499
end Delivery.IrregularNine14.P08
