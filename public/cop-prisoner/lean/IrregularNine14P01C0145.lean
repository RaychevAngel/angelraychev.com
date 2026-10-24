import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0095
import IrregularNine14P01C0096
import IrregularNine14P01C0097

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8700 : PairBound 9 := { available := 47, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 194 22 200 63 47 111 175 303), lower := (rows 305 194 22 200 16 32 64 128 256), losses := [] }

theorem u8700 : Upper (D 1) (R 1) [304,192,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8700
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8701 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 28 44 211 227 195 195 451), lower := (rows 305 194 28 44 16 32 64 128 256), losses := [] }

theorem u8701 : Upper (D 1) (R 1) [304,192,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8701
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8702 : PairBound 9 := { available := 166, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 305 194 28 73 182 166 230 166 422), lower := (rows 305 194 28 73 16 32 64 128 256), losses := [] }

theorem u8702 : Upper (D 1) (R 1) [304,192,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8702
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8703 : PairBound 9 := { available := 167, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 194 28 74 183 167 231 167 423), lower := (rows 305 194 28 74 16 32 64 128 256), losses := [] }

theorem u8703 : Upper (D 1) (R 1) [304,192,24,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8703
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8704 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 305 194 28 76 179 163 227 163 419), lower := (rows 305 194 28 76 16 32 64 128 256), losses := [] }

theorem u8704 : Upper (D 1) (R 1) [304,192,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8704
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8705 : Route 9 := (fun mask => (mask,id))

def c8705 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8705 : Upper (D 1) (R 1) [304,192,24,96] 13 := by
  apply FastRouting.sound _ _ [304,192,24,96] 13 (by decide) (choices 1) [1,2,4,128] r8705 c8705
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5731
  · exact u5732
  · exact u5733
  · exact u5734

def b8706 : PairBound 9 := { available := 39, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 194 28 200 55 39 103 167 295), lower := (rows 305 194 28 200 16 32 64 128 256), losses := [] }

theorem u8706 : Upper (D 1) (R 1) [304,192,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8706
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8707 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 52 73 158 174 206 142 398), lower := (rows 305 194 52 73 16 32 64 128 256), losses := [] }

theorem u8707 : Upper (D 1) (R 1) [304,192,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8707
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8708 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 52 76 155 171 203 139 395), lower := (rows 305 194 52 76 16 32 64 128 256), losses := [] }

theorem u8708 : Upper (D 1) (R 1) [304,192,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8708
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8709 : PairBound 9 := { available := 62, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 194 69 138 62 62 126 190 318), lower := (rows 305 194 69 138 16 32 64 128 256), losses := [] }

theorem u8709 : Upper (D 1) (R 1) [304,192,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8709
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8710 : Route 9 := (fun mask => (mask,id))

def c8710 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8710 : Upper (D 1) (R 1) [304,192,65,132] 13 := by
  apply FastRouting.sound _ _ [304,192,65,132] 13 (by decide) (choices 1) [2,8,32] r8710 c8710
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5735
  · exact u5736
  · exact u5737

def r8711 : Route 9 := (fun mask => (mask,id))

def c8711 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8711 : Upper (D 1) (R 1) [304,192,65,144] 13 := by
  apply FastRouting.sound _ _ [304,192,65,144] 13 (by decide) (choices 1) [2,4,8,32] r8711 c8711
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5738
  · exact u5739
  · exact u5740
  · exact u5741

def b8712 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 194 70 140 59 59 123 187 315), lower := (rows 305 194 70 140 16 32 64 128 256), losses := [] }

theorem u8712 : Upper (D 1) (R 1) [304,192,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8712
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8713 : PairBound 9 := { available := 47, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 194 70 152 63 47 111 175 303), lower := (rows 305 194 70 152 16 32 64 128 256), losses := [] }

theorem u8713 : Upper (D 1) (R 1) [304,192,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8713
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8714 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 305 194 76 140 51 51 115 179 307), lower := (rows 305 194 76 140 16 32 64 128 256), losses := [] }

theorem u8714 : Upper (D 1) (R 1) [304,192,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8714
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8715 : Route 9 := (fun mask => (mask,id))

def c8715 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8715 : Upper (D 1) (R 1) [304,192,72,144] 13 := by
  apply FastRouting.sound _ _ [304,192,72,144] 13 (by decide) (choices 1) [1,2,4,32] r8715 c8715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5742
  · exact u5743
  · exact u5744
  · exact u5745

def r8716 : Route 9 := (fun mask => (mask,id))

def c8716 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8716 : Upper (D 1) (R 1) [304,192,80,160] 13 := by
  apply FastRouting.sound _ _ [304,192,80,160] 13 (by decide) (choices 1) [1,2,4,8] r8716 c8716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5746
  · exact u5747
  · exact u5748
  · exact u5749

def b8717 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 19 22 488 496 480 480 480 480), lower := (rows 15 19 22 8 16 32 64 128 256), losses := [] }

theorem u8717 : Upper (D 1) (R 1) [14,17,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8717
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8718 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 15 19 38 504 496 496 496 496 496), lower := (rows 15 19 38 8 16 32 64 128 256), losses := [] }

theorem u8718 : Upper (D 1) (R 1) [14,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8718
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8719 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 19 52 490 498 482 482 482 482), lower := (rows 15 19 52 8 16 32 64 128 256), losses := [] }

theorem u8719 : Upper (D 1) (R 1) [14,17,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8719
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8720_18 : Upper (D 1) (R 1) [14,17,96,18] 13 :=
  permutation_upper _ _ _ [14,17,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5750

theorem m8720_34 : Upper (D 1) (R 1) [14,17,96,34] 13 :=
  permutation_upper _ _ _ [14,17,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5752

theorem m8720_48 : Upper (D 1) (R 1) [14,17,96,48] 13 :=
  permutation_upper _ _ _ [14,17,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5756

theorem m8720_130 : Upper (D 1) (R 1) [14,17,96,130] 13 :=
  permutation_upper _ _ _ [14,17,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5753

theorem m8720_144 : Upper (D 1) (R 1) [14,17,96,144] 13 :=
  permutation_upper _ _ _ [14,17,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5757

def r8720 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8720 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8720 : Upper (D 1) (R 1) [14,17,96] 13 := by
  apply FastRouting.sound _ _ [14,17,96] 13 (by decide) (choices 2) [18,34,48,96,130,144,160,258,272,288,384] r8720 c8720
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8720_18
  · exact m8720_34
  · exact m8720_48
  · exact u5760
  · exact m8720_130
  · exact m8720_144
  · exact u5761
  · exact u5762
  · exact u5763
  · exact u5764
  · exact u5765

def b8721 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 15 19 262 248 240 240 240 240 496), lower := (rows 15 19 262 8 16 32 64 128 256), losses := [] }

theorem u8721 : Upper (D 1) (R 1) [14,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8721
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8722 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 15 19 276 234 242 226 226 226 482), lower := (rows 15 19 276 8 16 32 64 128 256), losses := [] }

theorem u8722 : Upper (D 1) (R 1) [14,17,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8722
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8723_18 : Upper (D 1) (R 1) [14,17,288,18] 13 :=
  permutation_upper _ _ _ [14,17,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5751

theorem m8723_34 : Upper (D 1) (R 1) [14,17,288,34] 13 :=
  permutation_upper _ _ _ [14,17,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5754

theorem m8723_48 : Upper (D 1) (R 1) [14,17,288,48] 13 :=
  permutation_upper _ _ _ [14,17,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5758

theorem m8723_66 : Upper (D 1) (R 1) [14,17,288,66] 13 :=
  permutation_upper _ _ _ [14,17,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5755

theorem m8723_80 : Upper (D 1) (R 1) [14,17,288,80] 13 :=
  permutation_upper _ _ _ [14,17,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5759

theorem m8723_96 : Upper (D 1) (R 1) [14,17,288,96] 13 :=
  permutation_upper _ _ _ [14,17,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5764

theorem m8723_192 : Upper (D 1) (R 1) [14,17,288,192] 13 :=
  permutation_upper _ _ _ [14,17,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5765

def r8723 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8723 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8723 : Upper (D 1) (R 1) [14,17,288] 13 := by
  apply FastRouting.sound _ _ [14,17,288] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r8723 c8723
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8723_18
  · exact m8723_34
  · exact m8723_48
  · exact m8723_66
  · exact m8723_80
  · exact m8723_96
  · exact m8723_192

def b8724 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 15 50 7 504 496 496 496 496 496), lower := (rows 15 50 7 8 16 32 64 128 256), losses := [] }

theorem u8724 : Upper (D 1) (R 1) [14,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8724
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8725 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 21 490 498 482 482 482 482), lower := (rows 15 50 21 8 16 32 64 128 256), losses := [] }

theorem u8725 : Upper (D 1) (R 1) [14,48,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8725
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8726 : PairBound 9 := { available := 481, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 50 22 489 497 481 481 481 481), lower := (rows 15 50 22 8 16 32 64 128 256), losses := [] }

theorem u8726 : Upper (D 1) (R 1) [14,48,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8726
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8727 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 15 50 52 459 467 483 451 451 451), lower := (rows 15 50 52 8 16 32 64 128 256), losses := [] }

theorem u8727 : Upper (D 1) (R 1) [14,48,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8727
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8728_18 : Upper (D 1) (R 1) [14,48,65,18] 13 :=
  permutation_upper _ _ _ [14,48,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5770

theorem m8728_48 : Upper (D 1) (R 1) [14,48,65,48] 13 :=
  permutation_upper _ _ _ [14,48,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5774

def r8728 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8728 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8728 : Upper (D 1) (R 1) [14,48,65] 13 := by
  apply FastRouting.sound _ _ [14,48,65] 13 (by decide) (choices 2) [18,48,66,80,130,144,192,258,272,320,384] r8728 c8728
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8728_18
  · exact m8728_48
  · exact u5778
  · exact u5779
  · exact u5780
  · exact u5781
  · exact u5782
  · exact u5783
  · exact u5784
  · exact u5785
  · exact u5786

def b8729 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 15 50 70 505 497 497 497 497 497), lower := (rows 15 50 70 8 16 32 64 128 256), losses := [] }

theorem u8729 : Upper (D 1) (R 1) [14,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8729
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8730 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 84 491 499 483 483 483 483), lower := (rows 15 50 84 8 16 32 64 128 256), losses := [] }

theorem u8730 : Upper (D 1) (R 1) [14,48,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8730
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8731_3 : Upper (D 1) (R 1) [14,48,192,3] 13 :=
  permutation_upper _ _ _ [14,48,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5766

theorem m8731_17 : Upper (D 1) (R 1) [14,48,192,17] 13 :=
  permutation_upper _ _ _ [14,48,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5768

theorem m8731_18 : Upper (D 1) (R 1) [14,48,192,18] 13 :=
  permutation_upper _ _ _ [14,48,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5771

theorem m8731_48 : Upper (D 1) (R 1) [14,48,192,48] 13 :=
  permutation_upper _ _ _ [14,48,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5775

theorem m8731_65 : Upper (D 1) (R 1) [14,48,192,65] 13 :=
  permutation_upper _ _ _ [14,48,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5782

theorem m8731_66 : Upper (D 1) (R 1) [14,48,192,66] 13 :=
  permutation_upper _ _ _ [14,48,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5787

theorem m8731_80 : Upper (D 1) (R 1) [14,48,192,80] 13 :=
  permutation_upper _ _ _ [14,48,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5791

def r8731 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8731 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8731 : Upper (D 1) (R 1) [14,48,192] 13 := by
  apply FastRouting.sound _ _ [14,48,192] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192,257,258,272,320] r8731 c8731
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8731_3
  · exact m8731_17
  · exact m8731_18
  · exact m8731_48
  · exact m8731_65
  · exact m8731_66
  · exact m8731_80
  · exact u5795
  · exact u5796
  · exact u5797
  · exact u5798
  · exact u5799

theorem m8732_18 : Upper (D 1) (R 1) [14,48,257,18] 13 :=
  permutation_upper _ _ _ [14,48,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5772

theorem m8732_48 : Upper (D 1) (R 1) [14,48,257,48] 13 :=
  permutation_upper _ _ _ [14,48,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5776

theorem m8732_66 : Upper (D 1) (R 1) [14,48,257,66] 13 :=
  permutation_upper _ _ _ [14,48,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5788

theorem m8732_80 : Upper (D 1) (R 1) [14,48,257,80] 13 :=
  permutation_upper _ _ _ [14,48,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5792

theorem m8732_192 : Upper (D 1) (R 1) [14,48,257,192] 13 :=
  permutation_upper _ _ _ [14,48,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5796

def r8732 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8732 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8732 : Upper (D 1) (R 1) [14,48,257] 13 := by
  apply FastRouting.sound _ _ [14,48,257] 13 (by decide) (choices 2) [18,48,66,80,192] r8732 c8732
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m8732_18
  · exact m8732_48
  · exact m8732_66
  · exact m8732_80
  · exact m8732_192

def b8733 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 15 50 262 249 241 241 241 241 497), lower := (rows 15 50 262 8 16 32 64 128 256), losses := [] }

theorem u8733 : Upper (D 1) (R 1) [14,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8733
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8734 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 15 50 276 235 243 227 227 227 483), lower := (rows 15 50 276 8 16 32 64 128 256), losses := [] }

theorem u8734 : Upper (D 1) (R 1) [14,48,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8734
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8735_3 : Upper (D 1) (R 1) [14,48,320,3] 13 :=
  permutation_upper _ _ _ [14,48,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5767

theorem m8735_17 : Upper (D 1) (R 1) [14,48,320,17] 13 :=
  permutation_upper _ _ _ [14,48,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5769

theorem m8735_18 : Upper (D 1) (R 1) [14,48,320,18] 13 :=
  permutation_upper _ _ _ [14,48,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5773

theorem m8735_48 : Upper (D 1) (R 1) [14,48,320,48] 13 :=
  permutation_upper _ _ _ [14,48,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5777

theorem m8735_65 : Upper (D 1) (R 1) [14,48,320,65] 13 :=
  permutation_upper _ _ _ [14,48,65,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5785

theorem m8735_66 : Upper (D 1) (R 1) [14,48,320,66] 13 :=
  permutation_upper _ _ _ [14,48,66,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5789

theorem m8735_80 : Upper (D 1) (R 1) [14,48,320,80] 13 :=
  permutation_upper _ _ _ [14,48,80,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5793

theorem m8735_129 : Upper (D 1) (R 1) [14,48,320,129] 13 :=
  permutation_upper _ _ _ [14,48,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5786

theorem m8735_130 : Upper (D 1) (R 1) [14,48,320,130] 13 :=
  permutation_upper _ _ _ [14,48,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5790

theorem m8735_144 : Upper (D 1) (R 1) [14,48,320,144] 13 :=
  permutation_upper _ _ _ [14,48,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5794

theorem m8735_192 : Upper (D 1) (R 1) [14,48,320,192] 13 :=
  permutation_upper _ _ _ [14,48,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5799

def r8735 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8735 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8735 : Upper (D 1) (R 1) [14,48,320] 13 := by
  apply FastRouting.sound _ _ [14,48,320] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r8735 c8735
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8735_3
  · exact m8735_17
  · exact m8735_18
  · exact m8735_48
  · exact m8735_65
  · exact m8735_66
  · exact m8735_80
  · exact m8735_129
  · exact m8735_130
  · exact m8735_144
  · exact m8735_192

def b8736 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 15 259 22 248 240 240 240 240 496), lower := (rows 15 259 22 8 16 32 64 128 256), losses := [] }

theorem u8736 : Upper (D 1) (R 1) [14,257,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8736
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8737_18 : Upper (D 1) (R 1) [14,257,48,18] 13 :=
  permutation_upper _ _ _ [14,257,18,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5800

theorem m8737_66 : Upper (D 1) (R 1) [14,257,48,66] 13 :=
  permutation_upper _ _ _ [14,257,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5801

def r8737 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8737 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8737 : Upper (D 1) (R 1) [14,257,48] 13 := by
  apply FastRouting.sound _ _ [14,257,48] 13 (by decide) (choices 2) [18,48,66,80,192] r8737 c8737
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m8737_18
  · exact u5802
  · exact m8737_66
  · exact u5803
  · exact u5804

def b8738 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 15 274 7 248 240 240 240 240 496), lower := (rows 15 274 7 8 16 32 64 128 256), losses := [] }

theorem u8738 : Upper (D 1) (R 1) [14,272,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8738
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8739 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 15 274 21 234 242 226 226 226 482), lower := (rows 15 274 21 8 16 32 64 128 256), losses := [] }

theorem u8739 : Upper (D 1) (R 1) [14,272,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8739
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8740 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 274 22 233 241 225 225 225 481), lower := (rows 15 274 22 8 16 32 64 128 256), losses := [] }

theorem u8740 : Upper (D 1) (R 1) [14,272,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8740
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8741_18 : Upper (D 1) (R 1) [14,272,33,18] 13 :=
  permutation_upper _ _ _ [14,272,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5807

def r8741 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8741 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8741 : Upper (D 1) (R 1) [14,272,33] 13 := by
  apply FastRouting.sound _ _ [14,272,33] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r8741 c8741
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8741_18
  · exact u5809
  · exact u5810
  · exact u5811
  · exact u5812
  · exact u5813
  · exact u5814

def b8742 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 15 274 38 249 241 241 241 241 497), lower := (rows 15 274 38 8 16 32 64 128 256), losses := [] }

theorem u8742 : Upper (D 1) (R 1) [14,272,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8742
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8743 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 15 274 52 235 243 227 227 227 483), lower := (rows 15 274 52 8 16 32 64 128 256), losses := [] }

theorem u8743 : Upper (D 1) (R 1) [14,272,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8743
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8744_3 : Upper (D 1) (R 1) [14,272,96,3] 13 :=
  permutation_upper _ _ _ [14,272,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5805

theorem m8744_17 : Upper (D 1) (R 1) [14,272,96,17] 13 :=
  permutation_upper _ _ _ [14,272,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5806

theorem m8744_18 : Upper (D 1) (R 1) [14,272,96,18] 13 :=
  permutation_upper _ _ _ [14,272,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5808

theorem m8744_33 : Upper (D 1) (R 1) [14,272,96,33] 13 :=
  permutation_upper _ _ _ [14,272,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5813

theorem m8744_34 : Upper (D 1) (R 1) [14,272,96,34] 13 :=
  permutation_upper _ _ _ [14,272,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5815

theorem m8744_48 : Upper (D 1) (R 1) [14,272,96,48] 13 :=
  permutation_upper _ _ _ [14,272,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5817

theorem m8744_129 : Upper (D 1) (R 1) [14,272,96,129] 13 :=
  permutation_upper _ _ _ [14,272,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5814

theorem m8744_130 : Upper (D 1) (R 1) [14,272,96,130] 13 :=
  permutation_upper _ _ _ [14,272,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5816

theorem m8744_144 : Upper (D 1) (R 1) [14,272,96,144] 13 :=
  permutation_upper _ _ _ [14,272,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5818

def r8744 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8744 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8744 : Upper (D 1) (R 1) [14,272,96] 13 := by
  apply FastRouting.sound _ _ [14,272,96] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r8744 c8744
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8744_3
  · exact m8744_17
  · exact m8744_18
  · exact m8744_33
  · exact m8744_34
  · exact m8744_48
  · exact u5819
  · exact m8744_129
  · exact m8744_130
  · exact m8744_144
  · exact u5820

def b8745 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 23 11 22 488 496 480 480 480 480), lower := (rows 23 11 22 8 16 32 64 128 256), losses := [] }

theorem u8745 : Upper (D 1) (R 1) [22,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8745
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8746 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 23 11 38 504 496 496 496 496 496), lower := (rows 23 11 38 8 16 32 64 128 256), losses := [] }

theorem u8746 : Upper (D 1) (R 1) [22,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8746
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8747 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 490, targets := 16 }], pairs := [(1,4)], upper := (rows 23 11 52 490 498 482 482 482 482), lower := (rows 23 11 52 8 16 32 64 128 256), losses := [] }

theorem u8747 : Upper (D 1) (R 1) [22,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8747
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8748 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c8748 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8748 : Upper (D 1) (R 1) [22,9,96] 13 := by
  apply FastRouting.sound _ _ [22,9,96] 13 (by decide) (choices 2) [18,34,48,96,130,144,160,258,272,288,384] r8748 c8748
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5821
  · exact u5822
  · exact u5823
  · exact u5824
  · exact u5825
  · exact u5826
  · exact u5827
  · exact u5828
  · exact u5829
  · exact u5830
  · exact u5831

def b8749 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 23 11 262 248 240 240 240 240 496), lower := (rows 23 11 262 8 16 32 64 128 256), losses := [] }

theorem u8749 : Upper (D 1) (R 1) [22,9,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8749
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8750 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 23 11 276 234 242 226 226 226 482), lower := (rows 23 11 276 8 16 32 64 128 256), losses := [] }

theorem u8750 : Upper (D 1) (R 1) [22,9,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8750
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8751 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8751 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8751 : Upper (D 1) (R 1) [22,9,288] 13 := by
  apply FastRouting.sound _ _ [22,9,288] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r8751 c8751
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5832
  · exact u5833
  · exact u5834
  · exact u5835
  · exact u5836
  · exact u5837
  · exact u5838

def b8752 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 23 35 14 504 496 496 496 496 496), lower := (rows 23 35 14 8 16 32 64 128 256), losses := [] }

theorem u8752 : Upper (D 1) (R 1) [22,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8752
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8753 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 22 488 504 488 488 488 488), lower := (rows 23 35 22 8 16 32 64 128 256), losses := [] }

theorem u8753 : Upper (D 1) (R 1) [22,33,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8753
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8754 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 23 35 28 490 498 482 482 482 482), lower := (rows 23 35 28 8 16 32 64 128 256), losses := [] }

theorem u8754 : Upper (D 1) (R 1) [22,33,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8754
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8755 : PairBound 9 := { available := 472, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 23 35 38 472 472 504 472 472 472), lower := (rows 23 35 38 8 16 32 64 128 256), losses := [] }

theorem u8755 : Upper (D 1) (R 1) [22,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8755
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8756 : PairBound 9 := { available := 466, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 23 35 44 474 466 498 466 466 466), lower := (rows 23 35 44 8 16 32 64 128 256), losses := [] }

theorem u8756 : Upper (D 1) (R 1) [22,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8756
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8757 : PairBound 9 := { available := 458, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 23 35 52 458 474 490 458 458 458), lower := (rows 23 35 52 8 16 32 64 128 256), losses := [] }

theorem u8757 : Upper (D 1) (R 1) [22,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8757
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8758 : PairBound 9 := { available := 504, camps := [{ cop := 0, region := 488, targets := 2 }], pairs := [(3,1)], upper := (rows 23 35 70 504 504 504 504 504 504), lower := (rows 23 35 70 8 16 32 64 128 256), losses := [] }

theorem u8758 : Upper (D 1) (R 1) [22,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8758
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8759 : Route 9 := (fun mask => (mask,id))

def c8759 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8759 : Upper (D 1) (R 1) [22,33,72] 13 := by
  apply FastRouting.sound _ _ [22,33,72] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192,258,272,288,320,384] r8759 c8759
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5839
  · exact u5840
  · exact u5841
  · exact u5842
  · exact u5843
  · exact u5844
  · exact u5845
  · exact u5846
  · exact u5847
  · exact u5848
  · exact u5849
  · exact u5850
  · exact u5851
  · exact u5852
  · exact u5853

#print axioms u8759
end Delivery.IrregularNine14.P01
