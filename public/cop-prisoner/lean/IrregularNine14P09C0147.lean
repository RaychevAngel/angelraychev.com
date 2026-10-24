import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0112
import IrregularNine14P09C0113
import IrregularNine14P09C0114
import IrregularNine14P09C0115

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8820 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 8, targets := 385 },{ cop := 3, region := 4, targets := 129 }], pairs := [(2,0),(2,7),(3,0),(3,7),(3,8)], upper := (rows 7 26 100 104 401 417 449 385 385), lower := (rows 7 26 100 104 16 32 64 128 256), losses := [] }

theorem u8820 : Upper (D 9) (R 9) [6,24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8820 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8821_33 : Upper (D 9) (R 9) [6,24,96,129,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6748

theorem m8821_96 : Upper (D 9) (R 9) [6,24,96,129,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6751

def r8821 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8821 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8821 : Upper (D 9) (R 9) [6,24,96,129] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r8821 c8821
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8821_33
  · exact m8821_96
  · exact u6753
  · exact u6754
  · exact u6755
  · exact u6756
  · exact u6757

theorem m8822_65 : Upper (D 9) (R 9) [6,24,96,160,65] 13 :=
  permutation_upper _ _ _ [6,24,96,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6749

theorem m8822_129 : Upper (D 9) (R 9) [6,24,96,160,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6754

theorem m8822_257 : Upper (D 9) (R 9) [6,24,96,160,257] 13 :=
  permutation_upper _ _ _ [6,24,96,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6756

def r8822 : Route 9 := (fun mask => (mask,id))

def c8822 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8822 : Upper (D 9) (R 9) [6,24,96,160] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160] 13 (by decide) (choices 2) [65,129,192,257,320,384] r8822 c8822
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8822_65
  · exact m8822_129
  · exact u6758
  · exact m8822_257
  · exact u6759
  · exact u6760

theorem m8823_33 : Upper (D 9) (R 9) [6,24,96,384,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6750

theorem m8823_96 : Upper (D 9) (R 9) [6,24,96,384,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6752

theorem m8823_129 : Upper (D 9) (R 9) [6,24,96,384,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6757

theorem m8823_160 : Upper (D 9) (R 9) [6,24,96,384,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6760

def r8823 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8823 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8823 : Upper (D 9) (R 9) [6,24,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,384] 13 (by decide) (choices 2) [33,96,129,160,384] r8823 c8823
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m8823_33
  · exact m8823_96
  · exact m8823_129
  · exact m8823_160
  · exact u6761

def r8824 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8824 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8824 : Upper (D 9) (R 9) [6,33,65,48] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48] 13 (by decide) (choices 2) [72,136,192,384] r8824 c8824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6762
  · exact u6763
  · exact u6764
  · exact u6765

def b8825 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 69 104 408 440 472 408 408), lower := (rows 7 35 69 104 16 32 64 128 256), losses := [] }

theorem u8825 : Upper (D 9) (R 9) [6,33,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8825 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8826_40 : Upper (D 9) (R 9) [6,33,65,144,40] 13 :=
  permutation_upper _ _ _ [6,33,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6763

theorem m8826_72 : Upper (D 9) (R 9) [6,33,65,144,72] 13 :=
  permutation_upper _ _ _ [6,33,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6763

theorem m8826_96 : Upper (D 9) (R 9) [6,33,65,144,96] 13 :=
  permutation_upper _ _ _ [6,33,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6766

theorem m8826_192 : Upper (D 9) (R 9) [6,33,65,144,192] 13 :=
  permutation_upper _ _ _ [6,33,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6769

theorem m8826_320 : Upper (D 9) (R 9) [6,33,65,144,320] 13 :=
  permutation_upper _ _ _ [6,33,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6771

def r8826 : Route 9 := (fun mask => (mask,id))

def c8826 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8826 : Upper (D 9) (R 9) [6,33,65,144] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r8826 c8826
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8826_40
  · exact m8826_72
  · exact m8826_96
  · exact u6768
  · exact u6769
  · exact m8826_192
  · exact u6770
  · exact u6771
  · exact m8826_320
  · exact u6772

theorem m8827_72 : Upper (D 9) (R 9) [6,33,65,160,72] 13 :=
  permutation_upper _ _ _ [6,33,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6764

theorem m8827_136 : Upper (D 9) (R 9) [6,33,65,160,136] 13 :=
  permutation_upper _ _ _ [6,33,65,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6769

theorem m8827_264 : Upper (D 9) (R 9) [6,33,65,160,264] 13 :=
  permutation_upper _ _ _ [6,33,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6771

def r8827 : Route 9 := (fun mask => (mask,id))

def c8827 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8827 : Upper (D 9) (R 9) [6,33,65,160] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160] 13 (by decide) (choices 2) [72,136,192,264,320,384] r8827 c8827
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8827_72
  · exact m8827_136
  · exact u6773
  · exact m8827_264
  · exact u6774
  · exact u6775

theorem m8828_40 : Upper (D 9) (R 9) [6,33,65,384,40] 13 :=
  permutation_upper _ _ _ [6,33,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6765

theorem m8828_72 : Upper (D 9) (R 9) [6,33,65,384,72] 13 :=
  permutation_upper _ _ _ [6,33,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6765

theorem m8828_96 : Upper (D 9) (R 9) [6,33,65,384,96] 13 :=
  permutation_upper _ _ _ [6,33,65,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6767

theorem m8828_136 : Upper (D 9) (R 9) [6,33,65,384,136] 13 :=
  permutation_upper _ _ _ [6,33,65,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6772

theorem m8828_160 : Upper (D 9) (R 9) [6,33,65,384,160] 13 :=
  permutation_upper _ _ _ [6,33,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6775

theorem m8828_192 : Upper (D 9) (R 9) [6,33,65,384,192] 13 :=
  permutation_upper _ _ _ [6,33,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6775

def r8828 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8828 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8828 : Upper (D 9) (R 9) [6,33,65,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,384] 13 (by decide) (choices 2) [40,72,96,136,160,192,384] r8828 c8828
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8828_40
  · exact m8828_72
  · exact m8828_96
  · exact m8828_136
  · exact m8828_160
  · exact m8828_192
  · exact u6776

def r8829 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8829 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8829 : Upper (D 9) (R 9) [6,33,72,17] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17] 13 (by decide) (choices 2) [96,160,192,384] r8829 c8829
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6777
  · exact u6778
  · exact u6779
  · exact u6780

def b8830 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 8, targets := 448 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7),(3,8)], upper := (rows 7 35 76 41 464 496 464 464 464), lower := (rows 7 35 76 41 16 32 64 128 256), losses := [] }

theorem u8830 : Upper (D 9) (R 9) [6,33,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8830 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8831 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8831 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8831 : Upper (D 9) (R 9) [6,33,72,48] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48] 13 (by decide) (choices 2) [65,129,192,384] r8831 c8831
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6781
  · exact u6782
  · exact u6783
  · exact u6784

def b8832 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 435, targets := 64 },{ cop := 3, region := 4, targets := 160 }], pairs := [(0,6),(1,6),(2,5),(2,7),(4,6)], upper := (rows 7 35 76 73 432 432 496 432 432), lower := (rows 7 35 76 73 16 32 64 128 256), losses := [] }

theorem u8832 : Upper (D 9) (R 9) [6,33,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8832 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8833 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 4, targets := 417 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7),(2,8)], upper := (rows 7 35 76 88 433 417 481 417 417), lower := (rows 7 35 76 88 16 32 64 128 256), losses := [] }

theorem u8833 : Upper (D 9) (R 9) [6,33,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8833 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8834 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 76 104 401 433 465 401 401), lower := (rows 7 35 76 104 16 32 64 128 256), losses := [] }

theorem u8834 : Upper (D 9) (R 9) [6,33,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8834 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8835 : Route 9 := (fun mask => (mask,id))

def c8835 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8835 : Upper (D 9) (R 9) [6,33,72,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129] 13 (by decide) (choices 2) [96,160,192,288,320,384] r8835 c8835
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6785
  · exact u6786
  · exact u6787
  · exact u6788
  · exact u6789
  · exact u6790

def r8836 : Route 9 := (fun mask => (mask,id))

def c8836 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8836 : Upper (D 9) (R 9) [6,33,72,144] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r8836 c8836
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6791
  · exact u6792
  · exact u6793
  · exact u6794
  · exact u6795
  · exact u6796
  · exact u6797
  · exact u6798
  · exact u6799
  · exact u6800

def r8837 : Route 9 := (fun mask => (mask,id))

def c8837 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8837 : Upper (D 9) (R 9) [6,33,72,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160] 13 (by decide) (choices 2) [65,129,192,257,320,384] r8837 c8837
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6801
  · exact u6802
  · exact u6803
  · exact u6804
  · exact u6805
  · exact u6806

def b8838 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 4, targets := 417 },{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7),(2,8)], upper := (rows 7 35 76 200 433 433 497 433 433), lower := (rows 7 35 76 200 16 32 64 128 256), losses := [] }

theorem u8838 : Upper (D 9) (R 9) [6,33,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8838 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8839 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8839 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8839 : Upper (D 9) (R 9) [6,33,72,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r8839 c8839
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6807
  · exact u6808
  · exact u6809
  · exact u6810
  · exact u6811
  · exact u6812
  · exact u6813

def r8840 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8840 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8840 : Upper (D 9) (R 9) [6,33,192,17] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17] 13 (by decide) (choices 2) [40,72,96,192,264,288,320] r8840 c8840
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6814
  · exact u6815
  · exact u6816
  · exact u6817
  · exact u6818
  · exact u6819
  · exact u6820

def b8841 : PairBound 9 := { available := 472, camps := [{ cop := 1, region := 8, targets := 448 },{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7),(3,8)], upper := (rows 7 35 196 41 472 504 472 472 472), lower := (rows 7 35 196 41 16 32 64 128 256), losses := [] }

theorem u8841 : Upper (D 9) (R 9) [6,33,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8841 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8842_9 : Upper (D 9) (R 9) [6,33,192,48,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6814

def r8842 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8842 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8842 : Upper (D 9) (R 9) [6,33,192,48] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48] 13 (by decide) (choices 2) [9,65,72,192,257,264,320] r8842 c8842
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8842_9
  · exact u6824
  · exact u6825
  · exact u6826
  · exact u6827
  · exact u6828
  · exact u6829

theorem m8843_40 : Upper (D 9) (R 9) [6,33,192,65,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6824

def r8843 : Route 9 := (fun mask => (mask,id))

def c8843 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8843 : Upper (D 9) (R 9) [6,33,192,65] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65] 13 (by decide) (choices 2) [40,136,160,264,288,384] r8843 c8843
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8843_40
  · exact u6830
  · exact u6831
  · exact u6832
  · exact u6833
  · exact u6834

theorem m8844_9 : Upper (D 9) (R 9) [6,33,192,80,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6815

theorem m8844_33 : Upper (D 9) (R 9) [6,33,192,80,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6821

theorem m8844_40 : Upper (D 9) (R 9) [6,33,192,80,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6825

theorem m8844_129 : Upper (D 9) (R 9) [6,33,192,80,129] 13 :=
  permutation_upper _ _ _ [6,33,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6830

def r8844 : Route 9 := (fun mask => (mask,id))

def c8844 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8844 : Upper (D 9) (R 9) [6,33,192,80] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r8844 c8844
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8844_9
  · exact m8844_33
  · exact m8844_40
  · exact m8844_129
  · exact u6835
  · exact u6836
  · exact u6837
  · exact u6838
  · exact u6839
  · exact u6840

theorem m8845_9 : Upper (D 9) (R 9) [6,33,192,96,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6816

theorem m8845_129 : Upper (D 9) (R 9) [6,33,192,96,129] 13 :=
  permutation_upper _ _ _ [6,33,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6831

theorem m8845_136 : Upper (D 9) (R 9) [6,33,192,96,136] 13 :=
  permutation_upper _ _ _ [6,33,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6836

def r8845 : Route 9 := (fun mask => (mask,id))

def c8845 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8845 : Upper (D 9) (R 9) [6,33,192,96] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96] 13 (by decide) (choices 2) [9,129,136,257,264,384] r8845 c8845
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8845_9
  · exact m8845_129
  · exact m8845_136
  · exact u6841
  · exact u6842
  · exact u6843

def b8846 : PairBound 9 := { available := 313, camps := [{ cop := 2, region := 8, targets := 289 },{ cop := 3, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5),(3,8)], upper := (rows 7 35 196 200 313 313 377 441 313), lower := (rows 7 35 196 200 16 32 64 128 256), losses := [] }

theorem u8846 : Upper (D 9) (R 9) [6,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8846 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8847_40 : Upper (D 9) (R 9) [6,33,192,257,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6827

theorem m8847_72 : Upper (D 9) (R 9) [6,33,192,257,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6837

theorem m8847_96 : Upper (D 9) (R 9) [6,33,192,257,96] 13 :=
  permutation_upper _ _ _ [6,33,192,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6841

theorem m8847_192 : Upper (D 9) (R 9) [6,33,192,257,192] 13 :=
  permutation_upper _ _ _ [6,33,192,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6844

def r8847 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8847 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8847 : Upper (D 9) (R 9) [6,33,192,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,257] 13 (by decide) (choices 2) [40,72,96,192,264,288,320] r8847 c8847
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8847_40
  · exact m8847_72
  · exact m8847_96
  · exact m8847_192
  · exact u6847
  · exact u6848
  · exact u6849

theorem m8848_9 : Upper (D 9) (R 9) [6,33,192,272,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6818

theorem m8848_33 : Upper (D 9) (R 9) [6,33,192,272,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6822

theorem m8848_40 : Upper (D 9) (R 9) [6,33,192,272,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6828

theorem m8848_65 : Upper (D 9) (R 9) [6,33,192,272,65] 13 :=
  permutation_upper _ _ _ [6,33,192,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6832

theorem m8848_72 : Upper (D 9) (R 9) [6,33,192,272,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6838

theorem m8848_96 : Upper (D 9) (R 9) [6,33,192,272,96] 13 :=
  permutation_upper _ _ _ [6,33,192,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6842

theorem m8848_192 : Upper (D 9) (R 9) [6,33,192,272,192] 13 :=
  permutation_upper _ _ _ [6,33,192,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6845

theorem m8848_257 : Upper (D 9) (R 9) [6,33,192,272,257] 13 :=
  permutation_upper _ _ _ [6,33,192,257,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6847

def r8848 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8848 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8848 : Upper (D 9) (R 9) [6,33,192,272] 13 := by
  apply FastRouting.sound _ _ [6,33,192,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,192,257,264,288,320] r8848 c8848
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8848_9
  · exact m8848_33
  · exact m8848_40
  · exact m8848_65
  · exact m8848_72
  · exact m8848_96
  · exact m8848_192
  · exact m8848_257
  · exact u6850
  · exact u6851
  · exact u6852

theorem m8849_9 : Upper (D 9) (R 9) [6,33,192,288,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6819

theorem m8849_65 : Upper (D 9) (R 9) [6,33,192,288,65] 13 :=
  permutation_upper _ _ _ [6,33,192,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6833

theorem m8849_72 : Upper (D 9) (R 9) [6,33,192,288,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6839

theorem m8849_192 : Upper (D 9) (R 9) [6,33,192,288,192] 13 :=
  permutation_upper _ _ _ [6,33,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6846

theorem m8849_257 : Upper (D 9) (R 9) [6,33,192,288,257] 13 :=
  permutation_upper _ _ _ [6,33,192,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6848

theorem m8849_264 : Upper (D 9) (R 9) [6,33,192,288,264] 13 :=
  permutation_upper _ _ _ [6,33,192,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6851

def r8849 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8849 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8849 : Upper (D 9) (R 9) [6,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,288] 13 (by decide) (choices 2) [9,65,72,192,257,264,320] r8849 c8849
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8849_9
  · exact m8849_65
  · exact m8849_72
  · exact m8849_192
  · exact m8849_257
  · exact m8849_264
  · exact u6853

theorem m8850_9 : Upper (D 9) (R 9) [6,33,192,320,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6820

theorem m8850_33 : Upper (D 9) (R 9) [6,33,192,320,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6823

theorem m8850_40 : Upper (D 9) (R 9) [6,33,192,320,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6829

theorem m8850_129 : Upper (D 9) (R 9) [6,33,192,320,129] 13 :=
  permutation_upper _ _ _ [6,33,192,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6834

theorem m8850_136 : Upper (D 9) (R 9) [6,33,192,320,136] 13 :=
  permutation_upper _ _ _ [6,33,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6840

theorem m8850_160 : Upper (D 9) (R 9) [6,33,192,320,160] 13 :=
  permutation_upper _ _ _ [6,33,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6843

theorem m8850_257 : Upper (D 9) (R 9) [6,33,192,320,257] 13 :=
  permutation_upper _ _ _ [6,33,192,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6849

theorem m8850_264 : Upper (D 9) (R 9) [6,33,192,320,264] 13 :=
  permutation_upper _ _ _ [6,33,192,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6852

theorem m8850_288 : Upper (D 9) (R 9) [6,33,192,320,288] 13 :=
  permutation_upper _ _ _ [6,33,192,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6853

def r8850 : Route 9 := (fun mask => (mask,id))

def c8850 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8850 : Upper (D 9) (R 9) [6,33,192,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,320] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r8850 c8850
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8850_9
  · exact m8850_33
  · exact m8850_40
  · exact m8850_129
  · exact m8850_136
  · exact m8850_160
  · exact m8850_257
  · exact m8850_264
  · exact m8850_288
  · exact u6854

def r8851 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8851 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8851 : Upper (D 9) (R 9) [6,40,48,65] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65] 13 (by decide) (choices 2) [65,129,192,384] r8851 c8851
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6855
  · exact u6856
  · exact u6857
  · exact u6858

theorem m8852_65 : Upper (D 9) (R 9) [6,40,48,192,65] 13 :=
  permutation_upper _ _ _ [6,40,48,65,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6857

theorem m8852_257 : Upper (D 9) (R 9) [6,40,48,192,257] 13 :=
  permutation_upper _ _ _ [6,40,48,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6858

def r8852 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8852 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8852 : Upper (D 9) (R 9) [6,40,48,192] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192] 13 (by decide) (choices 2) [65,192,257,320] r8852 c8852
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m8852_65
  · exact u6859
  · exact m8852_257
  · exact u6860

def b8853 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 449 },{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(1,0),(1,6),(1,7),(1,8)], upper := (rows 7 42 84 41 465 481 449 449 449), lower := (rows 7 42 84 41 16 32 64 128 256), losses := [] }

theorem u8853 : Upper (D 9) (R 9) [6,40,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8853 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8854 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8854 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8854 : Upper (D 9) (R 9) [6,40,80,65] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65] 13 (by decide) (choices 2) [33,129,160,384] r8854 c8854
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6863
  · exact u6864
  · exact u6865
  · exact u6866

def b8855 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 2, targets := 449 },{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(1,0),(1,6),(1,7),(1,8)], upper := (rows 7 42 84 104 401 417 449 385 385), lower := (rows 7 42 84 104 16 32 64 128 256), losses := [] }

theorem u8855 : Upper (D 9) (R 9) [6,40,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8855 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8856_33 : Upper (D 9) (R 9) [6,40,80,129,33] 13 :=
  permutation_upper _ _ _ [6,40,80,65,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6864

theorem m8856_65 : Upper (D 9) (R 9) [6,40,80,129,65] 13 :=
  permutation_upper _ _ _ [6,40,80,33,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6861

theorem m8856_96 : Upper (D 9) (R 9) [6,40,80,129,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6867

def r8856 : Route 9 := (fun mask => (mask,id))

def c8856 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8856 : Upper (D 9) (R 9) [6,40,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r8856 c8856
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8856_33
  · exact m8856_65
  · exact m8856_96
  · exact u6869
  · exact u6870
  · exact u6871
  · exact u6872
  · exact u6873
  · exact u6874
  · exact u6875

def b8857 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 449 },{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(1,0),(1,6),(1,7),(1,8)], upper := (rows 7 42 84 168 465 481 449 449 449), lower := (rows 7 42 84 168 16 32 64 128 256), losses := [] }

theorem u8857 : Upper (D 9) (R 9) [6,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8857 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m8858_33 : Upper (D 9) (R 9) [6,40,80,192,33] 13 :=
  permutation_upper _ _ _ [6,40,80,65,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6865

theorem m8858_129 : Upper (D 9) (R 9) [6,40,80,192,129] 13 :=
  permutation_upper _ _ _ [6,40,80,129,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6870

theorem m8858_257 : Upper (D 9) (R 9) [6,40,80,192,257] 13 :=
  permutation_upper _ _ _ [6,40,80,129,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6873

def r8858 : Route 9 := (fun mask => (mask,id))

def c8858 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8858 : Upper (D 9) (R 9) [6,40,80,192] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192] 13 (by decide) (choices 2) [33,129,160,257,288,384] r8858 c8858
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8858_33
  · exact m8858_129
  · exact u6877
  · exact m8858_257
  · exact u6878
  · exact u6879

theorem m8859_33 : Upper (D 9) (R 9) [6,40,80,384,33] 13 :=
  permutation_upper _ _ _ [6,40,80,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6866

theorem m8859_65 : Upper (D 9) (R 9) [6,40,80,384,65] 13 :=
  permutation_upper _ _ _ [6,40,80,33,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6862

theorem m8859_96 : Upper (D 9) (R 9) [6,40,80,384,96] 13 :=
  permutation_upper _ _ _ [6,40,80,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6868

theorem m8859_129 : Upper (D 9) (R 9) [6,40,80,384,129] 13 :=
  permutation_upper _ _ _ [6,40,80,129,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6875

theorem m8859_160 : Upper (D 9) (R 9) [6,40,80,384,160] 13 :=
  permutation_upper _ _ _ [6,40,80,192,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6879

theorem m8859_192 : Upper (D 9) (R 9) [6,40,80,384,192] 13 :=
  permutation_upper _ _ _ [6,40,80,160,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6876

def r8859 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8859 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8859 : Upper (D 9) (R 9) [6,40,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r8859 c8859
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8859_33
  · exact m8859_65
  · exact m8859_96
  · exact m8859_129
  · exact m8859_160
  · exact m8859_192
  · exact u6880

def r8860 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8860 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8860 : Upper (D 9) (R 9) [6,40,96,17] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17] 13 (by decide) (choices 2) [65,129,192,384] r8860 c8860
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6881
  · exact u6882
  · exact u6883
  · exact u6884

def b8861 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 42 100 73 401 433 465 401 401), lower := (rows 7 42 100 73 16 32 64 128 256), losses := [] }

theorem u8861 : Upper (D 9) (R 9) [6,40,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8861 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8862 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8862 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8862 : Upper (D 9) (R 9) [6,40,96,80] 13 := by
  apply FastRouting.sound _ _ [6,40,96,80] 13 (by decide) (choices 2) [129,384] r8862 c8862
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6885
  · exact u6886

def r8863 : Route 9 := (fun mask => (mask,id))

def c8863 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8863 : Upper (D 9) (R 9) [6,40,96,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129] 13 (by decide) (choices 2) [65,129,192,257,320,384] r8863 c8863
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6887
  · exact u6888
  · exact u6889
  · exact u6890
  · exact u6891
  · exact u6892

def r8864 : Route 9 := (fun mask => (mask,id))

def c8864 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8864 : Upper (D 9) (R 9) [6,40,96,144] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144] 13 (by decide) (choices 2) [65,129,192,257,320,384] r8864 c8864
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6893
  · exact u6894
  · exact u6895
  · exact u6896
  · exact u6897
  · exact u6898

def r8865 : Route 9 := (fun mask => (mask,id))

def c8865 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8865 : Upper (D 9) (R 9) [6,40,96,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192] 13 (by decide) (choices 2) [129,257,384] r8865 c8865
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6899
  · exact u6900
  · exact u6901

def r8866 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8866 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8866 : Upper (D 9) (R 9) [6,40,96,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384] 13 (by decide) (choices 2) [65,129,192,384] r8866 c8866
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6902
  · exact u6903
  · exact u6904
  · exact u6905

def r8867 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8867 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8867 : Upper (D 9) (R 9) [6,40,192,17] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r8867 c8867
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6906
  · exact u6907
  · exact u6908
  · exact u6909
  · exact u6910
  · exact u6911
  · exact u6912

def b8868 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 2, targets := 449 },{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(1,0),(1,6),(1,7),(1,8)], upper := (rows 7 42 196 41 465 497 465 465 465), lower := (rows 7 42 196 41 16 32 64 128 256), losses := [] }

theorem u8868 : Upper (D 9) (R 9) [6,40,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8868 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8869 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 449 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(1,0),(1,6),(1,7),(1,8)], upper := (rows 7 42 196 56 465 481 449 449 449), lower := (rows 7 42 196 56 16 32 64 128 256), losses := [] }

theorem u8869 : Upper (D 9) (R 9) [6,40,192,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8869 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8870 : Route 9 := (fun mask => (mask,id))

def c8870 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8870 : Upper (D 9) (R 9) [6,40,192,65] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65] 13 (by decide) (choices 2) [33,129,160,257,288,384] r8870 c8870
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6913
  · exact u6914
  · exact u6915
  · exact u6916
  · exact u6917
  · exact u6918

def r8871 : Route 9 := (fun mask => (mask,id))

def c8871 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8871 : Upper (D 9) (R 9) [6,40,192,80] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80] 13 (by decide) (choices 2) [33,129,160,257,288,384] r8871 c8871
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6919
  · exact u6920
  · exact u6921
  · exact u6922
  · exact u6923
  · exact u6924

def b8872 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 2, targets := 449 },{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(1,0),(1,6),(1,7),(1,8)], upper := (rows 7 42 196 104 401 433 465 401 401), lower := (rows 7 42 196 104 16 32 64 128 256), losses := [] }

theorem u8872 : Upper (D 9) (R 9) [6,40,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8872 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8873 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 8, targets := 289 },{ cop := 3, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5),(3,8)], upper := (rows 7 42 196 200 305 305 369 433 305), lower := (rows 7 42 196 200 16 32 64 128 256), losses := [] }

theorem u8873 : Upper (D 9) (R 9) [6,40,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8873 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8874 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8874 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8874 : Upper (D 9) (R 9) [6,40,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r8874 c8874
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6925
  · exact u6926
  · exact u6927
  · exact u6928
  · exact u6929
  · exact u6930
  · exact u6931

def r8875 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8875 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u8875 : Upper (D 9) (R 9) [6,40,192,272] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r8875 c8875
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6932
  · exact u6933
  · exact u6934
  · exact u6935
  · exact u6936
  · exact u6937
  · exact u6938

def b8876 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 2, targets := 449 },{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(1,0),(1,6),(1,7),(1,8)], upper := (rows 7 42 196 296 465 497 465 465 465), lower := (rows 7 42 196 296 16 32 64 128 256), losses := [] }

theorem u8876 : Upper (D 9) (R 9) [6,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8876 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8877 : Route 9 := (fun mask => (mask,id))

def c8877 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8877 : Upper (D 9) (R 9) [6,40,192,320] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320] 13 (by decide) (choices 2) [33,129,160,257,288,384] r8877 c8877
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6939
  · exact u6940
  · exact u6941
  · exact u6942
  · exact u6943
  · exact u6944

theorem m8878_129 : Upper (D 9) (R 9) [6,96,160,17,129] 13 :=
  permutation_upper _ _ _ [6,96,160,17,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6946

theorem m8878_136 : Upper (D 9) (R 9) [6,96,160,17,136] 13 :=
  permutation_upper _ _ _ [6,96,160,17,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6947

theorem m8878_384 : Upper (D 9) (R 9) [6,96,160,17,384] 13 :=
  permutation_upper _ _ _ [6,96,160,17,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6951

def r8878 : Route 9 := (fun mask => (mask,id))

def c8878 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u8878 : Upper (D 9) (R 9) [6,96,160,17] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r8878 c8878
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6945
  · exact u6946
  · exact u6947
  · exact m8878_129
  · exact m8878_136
  · exact u6948
  · exact u6949
  · exact u6950
  · exact u6951
  · exact m8878_384

theorem m8879_9 : Upper (D 9) (R 9) [6,96,160,65,9] 13 :=
  permutation_upper _ _ _ [6,96,160,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6946

def r8879 : Route 9 := (fun mask => (mask,id))

def c8879 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8879 : Upper (D 9) (R 9) [6,96,160,65] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65] 13 (by decide) (choices 2) [9,129,136,257,264,384] r8879 c8879
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8879_9
  · exact u6952
  · exact u6953
  · exact u6954
  · exact u6955
  · exact u6956

#print axioms u8879
end Delivery.IrregularNine14.P09
