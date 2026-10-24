import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0072
import IrregularNine14P03C0073
import IrregularNine14P03C0074
import IrregularNine14P03C0075
import IrregularNine14P03C0078
import IrregularNine14P03C0079
import IrregularNine14P03C0080
import IrregularNine14P03C0081
import IrregularNine14P03C0082

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7020 : PairBound 9 := { available := 157, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 265 157 189 221 157 413), lower := (rows 97 98 134 265 16 32 64 128 256), losses := [] }

theorem u7020 : Upper (D 3) (R 3) [96,96,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7020
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7021 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 268 153 185 217 153 409), lower := (rows 97 98 134 268 16 32 64 128 256), losses := [] }

theorem u7021 : Upper (D 3) (R 3) [96,96,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7021
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7022 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 134 392 29 61 93 157 285), lower := (rows 97 98 134 392 16 32 64 128 256), losses := [] }

theorem u7022 : Upper (D 3) (R 3) [96,96,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7022
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7023 : PairBound 9 := { available := 151, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 140 265 151 183 215 151 407), lower := (rows 97 98 140 265 16 32 64 128 256), losses := [] }

theorem u7023 : Upper (D 3) (R 3) [96,96,136,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7023
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7024 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 140 266 149 181 213 149 405), lower := (rows 97 98 140 266 16 32 64 128 256), losses := [] }

theorem u7024 : Upper (D 3) (R 3) [96,96,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7024
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7025 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 97 98 140 268 147 179 211 147 403), lower := (rows 97 98 140 268 16 32 64 128 256), losses := [] }

theorem u7025 : Upper (D 3) (R 3) [96,96,136,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7025
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7026 : PairBound 9 := { available := 126, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 97 131 133 265 126 126 126 254 382), lower := (rows 97 131 133 265 16 32 64 128 256), losses := [] }

theorem u7026 : Upper (D 3) (R 3) [96,129,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7026
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7027 : PairBound 9 := { available := 125, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 97 131 133 266 125 125 125 253 381), lower := (rows 97 131 133 266 16 32 64 128 256), losses := [] }

theorem u7027 : Upper (D 3) (R 3) [96,129,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7027
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7028 : PairBound 9 := { available := 95, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 97 131 133 296 95 127 95 223 351), lower := (rows 97 131 133 296 16 32 64 128 256), losses := [] }

theorem u7028 : Upper (D 3) (R 3) [96,129,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7028
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7029 : PairBound 9 := { available := 125, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 131 134 265 125 125 125 253 381), lower := (rows 97 131 134 265 16 32 64 128 256), losses := [] }

theorem u7029 : Upper (D 3) (R 3) [96,129,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7029
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7030 : PairBound 9 := { available := 121, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 131 134 268 121 121 121 249 377), lower := (rows 97 131 134 268 16 32 64 128 256), losses := [] }

theorem u7030 : Upper (D 3) (R 3) [96,129,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7030
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7031 : PairBound 9 := { available := 93, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 131 134 296 93 125 93 221 349), lower := (rows 97 131 134 296 16 32 64 128 256), losses := [] }

theorem u7031 : Upper (D 3) (R 3) [96,129,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7031
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7032_3 : Upper (D 3) (R 3) [96,129,136,257,3] 13 :=
  permutation_upper _ _ _ [96,5,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4334

theorem m7032_5 : Upper (D 3) (R 3) [96,129,136,257,5] 13 :=
  permutation_upper _ _ _ [96,5,136,257,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4425

theorem m7032_6 : Upper (D 3) (R 3) [96,129,136,257,6] 13 :=
  permutation_upper _ _ _ [96,12,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4693

theorem m7032_33 : Upper (D 3) (R 3) [96,129,136,257,33] 13 :=
  permutation_upper _ _ _ [96,33,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4808

theorem m7032_34 : Upper (D 3) (R 3) [96,129,136,257,34] 13 :=
  permutation_upper _ _ _ [96,36,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4861

theorem m7032_36 : Upper (D 3) (R 3) [96,129,136,257,36] 13 :=
  permutation_upper _ _ _ [96,36,136,257,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4892

theorem m7032_96 : Upper (D 3) (R 3) [96,129,136,257,96] 13 :=
  permutation_upper _ _ _ [96,96,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4937

def r7032 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7032 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7032 : Upper (D 3) (R 3) [96,129,136,257] 13 := by
  apply FastRouting.sound _ _ [96,129,136,257] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r7032 c7032
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7032_3
  · exact m7032_5
  · exact m7032_6
  · exact m7032_33
  · exact m7032_34
  · exact m7032_36
  · exact m7032_96

def b7033 : PairBound 9 := { available := 117, camps := [{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 131 140 266 117 117 117 245 373), lower := (rows 97 131 140 266 16 32 64 128 256), losses := [] }

theorem u7033 : Upper (D 3) (R 3) [96,129,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7033
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7034 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 131 140 268 115 115 115 243 371), lower := (rows 97 131 140 268 16 32 64 128 256), losses := [] }

theorem u7034 : Upper (D 3) (R 3) [96,129,136,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7034
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7035_3 : Upper (D 3) (R 3) [96,129,136,272,3] 13 :=
  permutation_upper _ _ _ [96,5,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4335

theorem m7035_5 : Upper (D 3) (R 3) [96,129,136,272,5] 13 :=
  permutation_upper _ _ _ [96,5,136,258,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4430

theorem m7035_6 : Upper (D 3) (R 3) [96,129,136,272,6] 13 :=
  permutation_upper _ _ _ [96,12,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4694

theorem m7035_33 : Upper (D 3) (R 3) [96,129,136,272,33] 13 :=
  permutation_upper _ _ _ [96,33,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4809

theorem m7035_34 : Upper (D 3) (R 3) [96,129,136,272,34] 13 :=
  permutation_upper _ _ _ [96,36,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4862

theorem m7035_36 : Upper (D 3) (R 3) [96,129,136,272,36] 13 :=
  permutation_upper _ _ _ [96,36,136,258,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4895

theorem m7035_96 : Upper (D 3) (R 3) [96,129,136,272,96] 13 :=
  permutation_upper _ _ _ [96,96,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4938

def r7035 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7035 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7035 : Upper (D 3) (R 3) [96,129,136,272] 13 := by
  apply FastRouting.sound _ _ [96,129,136,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r7035 c7035
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7035_3
  · exact m7035_5
  · exact m7035_6
  · exact m7035_33
  · exact m7035_34
  · exact m7035_36
  · exact m7035_96

theorem m7036_3 : Upper (D 3) (R 3) [96,129,136,288,3] 13 :=
  permutation_upper _ _ _ [96,5,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4337

theorem m7036_5 : Upper (D 3) (R 3) [96,129,136,288,5] 13 :=
  permutation_upper _ _ _ [96,5,136,288,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4439

theorem m7036_6 : Upper (D 3) (R 3) [96,129,136,288,6] 13 :=
  permutation_upper _ _ _ [96,12,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4695

theorem m7036_65 : Upper (D 3) (R 3) [96,129,136,288,65] 13 :=
  permutation_upper _ _ _ [96,33,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4810

theorem m7036_66 : Upper (D 3) (R 3) [96,129,136,288,66] 13 :=
  permutation_upper _ _ _ [96,36,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4864

theorem m7036_68 : Upper (D 3) (R 3) [96,129,136,288,68] 13 :=
  permutation_upper _ _ _ [96,36,136,320,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4900

def r7036 : Route 9 := (fun mask => (mask,id))

def c7036 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7036 : Upper (D 3) (R 3) [96,129,136,288] 13 := by
  apply FastRouting.sound _ _ [96,129,136,288] 13 (by decide) (choices 2) [3,5,6,65,66,68] r7036 c7036
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7036_3
  · exact m7036_5
  · exact m7036_6
  · exact m7036_65
  · exact m7036_66
  · exact m7036_68

theorem m7037_3 : Upper (D 3) (R 3) [96,129,144,257,3] 13 :=
  permutation_upper _ _ _ [96,5,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4331

theorem m7037_5 : Upper (D 3) (R 3) [96,129,144,257,5] 13 :=
  permutation_upper _ _ _ [96,5,130,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4362

theorem m7037_6 : Upper (D 3) (R 3) [96,129,144,257,6] 13 :=
  permutation_upper _ _ _ [96,12,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4690

theorem m7037_9 : Upper (D 3) (R 3) [96,129,144,257,9] 13 :=
  permutation_upper _ _ _ [96,5,257,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4487

theorem m7037_10 : Upper (D 3) (R 3) [96,129,144,257,10] 13 :=
  permutation_upper _ _ _ [96,12,129,257,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4704

theorem m7037_12 : Upper (D 3) (R 3) [96,129,144,257,12] 13 :=
  permutation_upper _ _ _ [96,12,130,257,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4728

theorem m7037_33 : Upper (D 3) (R 3) [96,129,144,257,33] 13 :=
  permutation_upper _ _ _ [96,33,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4804

theorem m7037_34 : Upper (D 3) (R 3) [96,129,144,257,34] 13 :=
  permutation_upper _ _ _ [96,36,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4858

theorem m7037_36 : Upper (D 3) (R 3) [96,129,144,257,36] 13 :=
  permutation_upper _ _ _ [96,36,130,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4870

theorem m7037_40 : Upper (D 3) (R 3) [96,129,144,257,40] 13 :=
  permutation_upper _ _ _ [96,36,257,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4911

theorem m7037_96 : Upper (D 3) (R 3) [96,129,144,257,96] 13 :=
  permutation_upper _ _ _ [96,96,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4934

def r7037 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7037 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7037 : Upper (D 3) (R 3) [96,129,144,257] 13 := by
  apply FastRouting.sound _ _ [96,129,144,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,96] r7037 c7037
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7037_3
  · exact m7037_5
  · exact m7037_6
  · exact m7037_9
  · exact m7037_10
  · exact m7037_12
  · exact m7037_33
  · exact m7037_34
  · exact m7037_36
  · exact m7037_40
  · exact m7037_96

theorem m7038_5 : Upper (D 3) (R 3) [96,129,144,258,5] 13 :=
  permutation_upper _ _ _ [96,5,130,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4363

theorem m7038_9 : Upper (D 3) (R 3) [96,129,144,258,9] 13 :=
  permutation_upper _ _ _ [96,5,264,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4527

theorem m7038_12 : Upper (D 3) (R 3) [96,129,144,258,12] 13 :=
  permutation_upper _ _ _ [96,12,130,272,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4732

theorem m7038_33 : Upper (D 3) (R 3) [96,129,144,258,33] 13 :=
  permutation_upper _ _ _ [96,33,129,130,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4805

theorem m7038_36 : Upper (D 3) (R 3) [96,129,144,258,36] 13 :=
  permutation_upper _ _ _ [96,36,130,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4871

theorem m7038_40 : Upper (D 3) (R 3) [96,129,144,258,40] 13 :=
  permutation_upper _ _ _ [96,36,264,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4920

theorem m7038_96 : Upper (D 3) (R 3) [96,129,144,258,96] 13 :=
  permutation_upper _ _ _ [96,96,129,130,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4935

def r7038 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7038 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7038 : Upper (D 3) (R 3) [96,129,144,258] 13 := by
  apply FastRouting.sound _ _ [96,129,144,258] 13 (by decide) (choices 2) [5,9,12,33,36,40,96] r7038 c7038
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7038_5
  · exact m7038_9
  · exact m7038_12
  · exact m7038_33
  · exact m7038_36
  · exact m7038_40
  · exact m7038_96

theorem m7039_3 : Upper (D 3) (R 3) [96,129,144,260,3] 13 :=
  permutation_upper _ _ _ [96,5,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4332

theorem m7039_9 : Upper (D 3) (R 3) [96,129,144,260,9] 13 :=
  permutation_upper _ _ _ [96,5,264,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4531

theorem m7039_10 : Upper (D 3) (R 3) [96,129,144,260,10] 13 :=
  permutation_upper _ _ _ [96,12,129,272,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4714

theorem m7039_33 : Upper (D 3) (R 3) [96,129,144,260,33] 13 :=
  permutation_upper _ _ _ [96,33,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4806

theorem m7039_34 : Upper (D 3) (R 3) [96,129,144,260,34] 13 :=
  permutation_upper _ _ _ [96,36,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4859

theorem m7039_40 : Upper (D 3) (R 3) [96,129,144,260,40] 13 :=
  permutation_upper _ _ _ [96,36,264,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4922

theorem m7039_96 : Upper (D 3) (R 3) [96,129,144,260,96] 13 :=
  permutation_upper _ _ _ [96,96,129,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4936

def r7039 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7039 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7039 : Upper (D 3) (R 3) [96,129,144,260] 13 := by
  apply FastRouting.sound _ _ [96,129,144,260] 13 (by decide) (choices 2) [3,9,10,33,34,40,96] r7039 c7039
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7039_3
  · exact m7039_9
  · exact m7039_10
  · exact m7039_33
  · exact m7039_34
  · exact m7039_40
  · exact m7039_96

theorem m7040_3 : Upper (D 3) (R 3) [96,129,144,288,3] 13 :=
  permutation_upper _ _ _ [96,5,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4333

theorem m7040_5 : Upper (D 3) (R 3) [96,129,144,288,5] 13 :=
  permutation_upper _ _ _ [96,5,130,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4364

theorem m7040_6 : Upper (D 3) (R 3) [96,129,144,288,6] 13 :=
  permutation_upper _ _ _ [96,12,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4691

theorem m7040_9 : Upper (D 3) (R 3) [96,129,144,288,9] 13 :=
  permutation_upper _ _ _ [96,5,288,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4550

theorem m7040_10 : Upper (D 3) (R 3) [96,129,144,288,10] 13 :=
  permutation_upper _ _ _ [96,12,129,288,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4719

theorem m7040_12 : Upper (D 3) (R 3) [96,129,144,288,12] 13 :=
  permutation_upper _ _ _ [96,12,130,288,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4734

theorem m7040_65 : Upper (D 3) (R 3) [96,129,144,288,65] 13 :=
  permutation_upper _ _ _ [96,33,129,130,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4807

theorem m7040_66 : Upper (D 3) (R 3) [96,129,144,288,66] 13 :=
  permutation_upper _ _ _ [96,36,129,130,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4860

theorem m7040_68 : Upper (D 3) (R 3) [96,129,144,288,68] 13 :=
  permutation_upper _ _ _ [96,36,130,129,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4872

theorem m7040_72 : Upper (D 3) (R 3) [96,129,144,288,72] 13 :=
  permutation_upper _ _ _ [96,36,320,129,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4930

def r7040 : Route 9 := (fun mask => (mask,id))

def c7040 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7040 : Upper (D 3) (R 3) [96,129,144,288] 13 := by
  apply FastRouting.sound _ _ [96,129,144,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r7040 c7040
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7040_3
  · exact m7040_5
  · exact m7040_6
  · exact m7040_9
  · exact m7040_10
  · exact m7040_12
  · exact m7040_65
  · exact m7040_66
  · exact m7040_68
  · exact m7040_72

theorem m7041_3 : Upper (D 3) (R 3) [96,129,160,257,3] 13 :=
  permutation_upper _ _ _ [96,5,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4338

theorem m7041_5 : Upper (D 3) (R 3) [96,129,160,257,5] 13 :=
  permutation_upper _ _ _ [96,5,160,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4463

theorem m7041_6 : Upper (D 3) (R 3) [96,129,160,257,6] 13 :=
  permutation_upper _ _ _ [96,12,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4697

theorem m7041_9 : Upper (D 3) (R 3) [96,129,160,257,9] 13 :=
  permutation_upper _ _ _ [96,5,257,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4488

theorem m7041_10 : Upper (D 3) (R 3) [96,129,160,257,10] 13 :=
  permutation_upper _ _ _ [96,12,129,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4705

theorem m7041_12 : Upper (D 3) (R 3) [96,129,160,257,12] 13 :=
  permutation_upper _ _ _ [96,12,160,257,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4760

theorem m7041_65 : Upper (D 3) (R 3) [96,129,160,257,65] 13 :=
  permutation_upper _ _ _ [96,33,129,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4811

theorem m7041_66 : Upper (D 3) (R 3) [96,129,160,257,66] 13 :=
  permutation_upper _ _ _ [96,36,129,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4865

theorem m7041_68 : Upper (D 3) (R 3) [96,129,160,257,68] 13 :=
  permutation_upper _ _ _ [96,36,192,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4902

theorem m7041_72 : Upper (D 3) (R 3) [96,129,160,257,72] 13 :=
  permutation_upper _ _ _ [96,36,257,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4913

def r7041 : Route 9 := (fun mask => (mask,id))

def c7041 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7041 : Upper (D 3) (R 3) [96,129,160,257] 13 := by
  apply FastRouting.sound _ _ [96,129,160,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r7041 c7041
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7041_3
  · exact m7041_5
  · exact m7041_6
  · exact m7041_9
  · exact m7041_10
  · exact m7041_12
  · exact m7041_65
  · exact m7041_66
  · exact m7041_68
  · exact m7041_72

theorem m7042_5 : Upper (D 3) (R 3) [96,129,160,258,5] 13 :=
  permutation_upper _ _ _ [96,5,160,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4465

theorem m7042_9 : Upper (D 3) (R 3) [96,129,160,258,9] 13 :=
  permutation_upper _ _ _ [96,5,264,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4528

theorem m7042_12 : Upper (D 3) (R 3) [96,129,160,258,12] 13 :=
  permutation_upper _ _ _ [96,12,160,272,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4767

theorem m7042_65 : Upper (D 3) (R 3) [96,129,160,258,65] 13 :=
  permutation_upper _ _ _ [96,33,129,192,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4813

theorem m7042_68 : Upper (D 3) (R 3) [96,129,160,258,68] 13 :=
  permutation_upper _ _ _ [96,36,192,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4904

theorem m7042_72 : Upper (D 3) (R 3) [96,129,160,258,72] 13 :=
  permutation_upper _ _ _ [96,36,264,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4921

def r7042 : Route 9 := (fun mask => (mask,id))

def c7042 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7042 : Upper (D 3) (R 3) [96,129,160,258] 13 := by
  apply FastRouting.sound _ _ [96,129,160,258] 13 (by decide) (choices 2) [5,9,12,65,68,72] r7042 c7042
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7042_5
  · exact m7042_9
  · exact m7042_12
  · exact m7042_65
  · exact m7042_68
  · exact m7042_72

theorem m7043_3 : Upper (D 3) (R 3) [96,129,160,260,3] 13 :=
  permutation_upper _ _ _ [96,5,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4340

theorem m7043_9 : Upper (D 3) (R 3) [96,129,160,260,9] 13 :=
  permutation_upper _ _ _ [96,5,264,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4540

theorem m7043_10 : Upper (D 3) (R 3) [96,129,160,260,10] 13 :=
  permutation_upper _ _ _ [96,12,129,272,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4715

theorem m7043_65 : Upper (D 3) (R 3) [96,129,160,260,65] 13 :=
  permutation_upper _ _ _ [96,33,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4814

theorem m7043_66 : Upper (D 3) (R 3) [96,129,160,260,66] 13 :=
  permutation_upper _ _ _ [96,36,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4867

theorem m7043_72 : Upper (D 3) (R 3) [96,129,160,260,72] 13 :=
  permutation_upper _ _ _ [96,36,264,192,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4927

def r7043 : Route 9 := (fun mask => (mask,id))

def c7043 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7043 : Upper (D 3) (R 3) [96,129,160,260] 13 := by
  apply FastRouting.sound _ _ [96,129,160,260] 13 (by decide) (choices 2) [3,9,10,65,66,72] r7043 c7043
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7043_3
  · exact m7043_9
  · exact m7043_10
  · exact m7043_65
  · exact m7043_66
  · exact m7043_72

theorem m7044_3 : Upper (D 3) (R 3) [96,129,160,272,3] 13 :=
  permutation_upper _ _ _ [96,5,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4339

theorem m7044_5 : Upper (D 3) (R 3) [96,129,160,272,5] 13 :=
  permutation_upper _ _ _ [96,5,160,129,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4464

theorem m7044_6 : Upper (D 3) (R 3) [96,129,160,272,6] 13 :=
  permutation_upper _ _ _ [96,12,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4698

theorem m7044_9 : Upper (D 3) (R 3) [96,129,160,272,9] 13 :=
  permutation_upper _ _ _ [96,5,258,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4503

theorem m7044_10 : Upper (D 3) (R 3) [96,129,160,272,10] 13 :=
  permutation_upper _ _ _ [96,12,129,258,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4709

theorem m7044_12 : Upper (D 3) (R 3) [96,129,160,272,12] 13 :=
  permutation_upper _ _ _ [96,12,160,258,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4763

theorem m7044_65 : Upper (D 3) (R 3) [96,129,160,272,65] 13 :=
  permutation_upper _ _ _ [96,33,129,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4812

theorem m7044_66 : Upper (D 3) (R 3) [96,129,160,272,66] 13 :=
  permutation_upper _ _ _ [96,36,129,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4866

theorem m7044_68 : Upper (D 3) (R 3) [96,129,160,272,68] 13 :=
  permutation_upper _ _ _ [96,36,192,129,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4903

theorem m7044_72 : Upper (D 3) (R 3) [96,129,160,272,72] 13 :=
  permutation_upper _ _ _ [96,36,258,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4918

def r7044 : Route 9 := (fun mask => (mask,id))

def c7044 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7044 : Upper (D 3) (R 3) [96,129,160,272] 13 := by
  apply FastRouting.sound _ _ [96,129,160,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r7044 c7044
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7044_3
  · exact m7044_5
  · exact m7044_6
  · exact m7044_9
  · exact m7044_10
  · exact m7044_12
  · exact m7044_65
  · exact m7044_66
  · exact m7044_68
  · exact m7044_72

theorem m7045_3 : Upper (D 3) (R 3) [96,129,160,320,3] 13 :=
  permutation_upper _ _ _ [96,5,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4341

theorem m7045_5 : Upper (D 3) (R 3) [96,129,160,320,5] 13 :=
  permutation_upper _ _ _ [96,5,160,129,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4466

theorem m7045_6 : Upper (D 3) (R 3) [96,129,160,320,6] 13 :=
  permutation_upper _ _ _ [96,12,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4699

theorem m7045_9 : Upper (D 3) (R 3) [96,129,160,320,9] 13 :=
  permutation_upper _ _ _ [96,5,288,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4551

theorem m7045_10 : Upper (D 3) (R 3) [96,129,160,320,10] 13 :=
  permutation_upper _ _ _ [96,12,129,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4720

theorem m7045_12 : Upper (D 3) (R 3) [96,129,160,320,12] 13 :=
  permutation_upper _ _ _ [96,12,160,320,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4770

def r7045 : Route 9 := (fun mask => (mask,id))

def c7045 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u7045 : Upper (D 3) (R 3) [96,129,160,320] 13 := by
  apply FastRouting.sound _ _ [96,129,160,320] 13 (by decide) (choices 2) [3,5,6,9,10,12] r7045 c7045
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7045_3
  · exact m7045_5
  · exact m7045_6
  · exact m7045_9
  · exact m7045_10
  · exact m7045_12

def b7046 : PairBound 9 := { available := 121, camps := [{ cop := 7, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 134 134 265 121 121 121 249 377), lower := (rows 97 134 134 265 16 32 64 128 256), losses := [] }

theorem u7046 : Upper (D 3) (R 3) [96,132,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7046
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7047 : PairBound 9 := { available := 89, camps := [{ cop := 7, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 134 134 296 89 121 89 217 345), lower := (rows 97 134 134 296 16 32 64 128 256), losses := [] }

theorem u7047 : Upper (D 3) (R 3) [96,132,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7047
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7048 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 140 265 115 115 115 243 371), lower := (rows 97 134 140 265 16 32 64 128 256), losses := [] }

theorem u7048 : Upper (D 3) (R 3) [96,132,136,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7048
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7049 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 140 266 113 113 113 241 369), lower := (rows 97 134 140 266 16 32 64 128 256), losses := [] }

theorem u7049 : Upper (D 3) (R 3) [96,132,136,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7049
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7050 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 140 296 83 115 83 211 339), lower := (rows 97 134 140 296 16 32 64 128 256), losses := [] }

theorem u7050 : Upper (D 3) (R 3) [96,132,136,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7050
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7051 : PairBound 9 := { available := 107, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 148 265 123 107 107 235 363), lower := (rows 97 134 148 265 16 32 64 128 256), losses := [] }

theorem u7051 : Upper (D 3) (R 3) [96,132,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7051
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7052 : PairBound 9 := { available := 105, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 148 266 121 105 105 233 361), lower := (rows 97 134 148 266 16 32 64 128 256), losses := [] }

theorem u7052 : Upper (D 3) (R 3) [96,132,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7052
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7053 : PairBound 9 := { available := 75, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 148 296 91 107 75 203 331), lower := (rows 97 134 148 296 16 32 64 128 256), losses := [] }

theorem u7053 : Upper (D 3) (R 3) [96,132,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7053
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7054 : PairBound 9 := { available := 91, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 164 265 91 123 91 219 347), lower := (rows 97 134 164 265 16 32 64 128 256), losses := [] }

theorem u7054 : Upper (D 3) (R 3) [96,132,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7054
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7055 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 164 266 89 121 89 217 345), lower := (rows 97 134 164 266 16 32 64 128 256), losses := [] }

theorem u7055 : Upper (D 3) (R 3) [96,132,160,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7055
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7056 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 164 328 27 59 91 155 283), lower := (rows 97 134 164 328 16 32 64 128 256), losses := [] }

theorem u7056 : Upper (D 3) (R 3) [96,132,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7056
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7057_3 : Upper (D 3) (R 3) [96,132,257,144,3] 13 :=
  permutation_upper _ _ _ [96,5,136,257,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4426

theorem m7057_9 : Upper (D 3) (R 3) [96,132,257,144,9] 13 :=
  permutation_upper _ _ _ [96,5,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4365

theorem m7057_10 : Upper (D 3) (R 3) [96,132,257,144,10] 13 :=
  permutation_upper _ _ _ [96,12,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4722

theorem m7057_33 : Upper (D 3) (R 3) [96,132,257,144,33] 13 :=
  permutation_upper _ _ _ [96,33,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4815

theorem m7057_34 : Upper (D 3) (R 3) [96,132,257,144,34] 13 :=
  permutation_upper _ _ _ [96,36,136,257,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4893

theorem m7057_40 : Upper (D 3) (R 3) [96,132,257,144,40] 13 :=
  permutation_upper _ _ _ [96,36,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4873

theorem m7057_96 : Upper (D 3) (R 3) [96,132,257,144,96] 13 :=
  permutation_upper _ _ _ [96,96,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4939

def r7057 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7057 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7057 : Upper (D 3) (R 3) [96,132,257,144] 13 := by
  apply FastRouting.sound _ _ [96,132,257,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,96] r7057 c7057
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7057_3
  · exact m7057_9
  · exact m7057_10
  · exact m7057_33
  · exact m7057_34
  · exact m7057_40
  · exact m7057_96

theorem m7058_3 : Upper (D 3) (R 3) [96,132,257,160,3] 13 :=
  permutation_upper _ _ _ [96,5,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4427

theorem m7058_9 : Upper (D 3) (R 3) [96,132,257,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4470

theorem m7058_10 : Upper (D 3) (R 3) [96,132,257,160,10] 13 :=
  permutation_upper _ _ _ [96,12,144,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4737

theorem m7058_65 : Upper (D 3) (R 3) [96,132,257,160,65] 13 :=
  permutation_upper _ _ _ [96,33,136,257,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4820

theorem m7058_66 : Upper (D 3) (R 3) [96,132,257,160,66] 13 :=
  permutation_upper _ _ _ [96,36,136,257,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4894

theorem m7058_72 : Upper (D 3) (R 3) [96,132,257,160,72] 13 :=
  permutation_upper _ _ _ [96,36,192,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4907

def r7058 : Route 9 := (fun mask => (mask,id))

def c7058 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7058 : Upper (D 3) (R 3) [96,132,257,160] 13 := by
  apply FastRouting.sound _ _ [96,132,257,160] 13 (by decide) (choices 2) [3,9,10,65,66,72] r7058 c7058
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7058_3
  · exact m7058_9
  · exact m7058_10
  · exact m7058_65
  · exact m7058_66
  · exact m7058_72

def b7059 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 262 152 121 105 105 233 361), lower := (rows 97 134 262 152 16 32 64 128 256), losses := [] }

theorem u7059 : Upper (D 3) (R 3) [96,132,258,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7059
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7060 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 262 168 89 121 89 217 345), lower := (rows 97 134 262 168 16 32 64 128 256), losses := [] }

theorem u7060 : Upper (D 3) (R 3) [96,132,258,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7060
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7061 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 268 152 115 99 99 227 355), lower := (rows 97 134 268 152 16 32 64 128 256), losses := [] }

theorem u7061 : Upper (D 3) (R 3) [96,132,264,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7061
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7062 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 268 168 83 115 83 211 339), lower := (rows 97 134 268 168 16 32 64 128 256), losses := [] }

theorem u7062 : Upper (D 3) (R 3) [96,132,264,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7062
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7063_3 : Upper (D 3) (R 3) [96,132,272,160,3] 13 :=
  permutation_upper _ _ _ [96,5,136,258,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4431

theorem m7063_9 : Upper (D 3) (R 3) [96,132,272,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4471

theorem m7063_10 : Upper (D 3) (R 3) [96,132,272,160,10] 13 :=
  permutation_upper _ _ _ [96,12,144,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4738

theorem m7063_65 : Upper (D 3) (R 3) [96,132,272,160,65] 13 :=
  permutation_upper _ _ _ [96,33,136,258,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4821

theorem m7063_66 : Upper (D 3) (R 3) [96,132,272,160,66] 13 :=
  permutation_upper _ _ _ [96,36,136,258,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4896

theorem m7063_72 : Upper (D 3) (R 3) [96,132,272,160,72] 13 :=
  permutation_upper _ _ _ [96,36,192,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4908

def r7063 : Route 9 := (fun mask => (mask,id))

def c7063 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7063 : Upper (D 3) (R 3) [96,132,272,160] 13 := by
  apply FastRouting.sound _ _ [96,132,272,160] 13 (by decide) (choices 2) [3,9,10,65,66,72] r7063 c7063
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7063_3
  · exact m7063_9
  · exact m7063_10
  · exact m7063_65
  · exact m7063_66
  · exact m7063_72

theorem m7064_3 : Upper (D 3) (R 3) [96,132,288,144,3] 13 :=
  permutation_upper _ _ _ [96,5,136,288,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4440

theorem m7064_9 : Upper (D 3) (R 3) [96,132,288,144,9] 13 :=
  permutation_upper _ _ _ [96,5,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4367

theorem m7064_10 : Upper (D 3) (R 3) [96,132,288,144,10] 13 :=
  permutation_upper _ _ _ [96,12,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4723

theorem m7064_65 : Upper (D 3) (R 3) [96,132,288,144,65] 13 :=
  permutation_upper _ _ _ [96,33,130,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4816

theorem m7064_66 : Upper (D 3) (R 3) [96,132,288,144,66] 13 :=
  permutation_upper _ _ _ [96,36,136,320,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4901

theorem m7064_72 : Upper (D 3) (R 3) [96,132,288,144,72] 13 :=
  permutation_upper _ _ _ [96,36,130,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4875

def r7064 : Route 9 := (fun mask => (mask,id))

def c7064 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7064 : Upper (D 3) (R 3) [96,132,288,144] 13 := by
  apply FastRouting.sound _ _ [96,132,288,144] 13 (by decide) (choices 2) [3,9,10,65,66,72] r7064 c7064
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7064_3
  · exact m7064_9
  · exact m7064_10
  · exact m7064_65
  · exact m7064_66
  · exact m7064_72

theorem m7065_3 : Upper (D 3) (R 3) [96,132,288,192,3] 13 :=
  permutation_upper _ _ _ [96,5,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4441

theorem m7065_9 : Upper (D 3) (R 3) [96,132,288,192,9] 13 :=
  permutation_upper _ _ _ [96,5,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4473

theorem m7065_10 : Upper (D 3) (R 3) [96,132,288,192,10] 13 :=
  permutation_upper _ _ _ [96,12,144,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4739

def r7065 : Route 9 := (fun mask => (mask,id))

def c7065 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u7065 : Upper (D 3) (R 3) [96,132,288,192] 13 := by
  apply FastRouting.sound _ _ [96,132,288,192] 13 (by decide) (choices 2) [3,9,10] r7065 c7065
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m7065_3
  · exact m7065_9
  · exact m7065_10

theorem m7066_3 : Upper (D 3) (R 3) [96,144,160,257,3] 13 :=
  permutation_upper _ _ _ [96,5,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4368

theorem m7066_5 : Upper (D 3) (R 3) [96,144,160,257,5] 13 :=
  permutation_upper _ _ _ [96,5,160,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4467

theorem m7066_6 : Upper (D 3) (R 3) [96,144,160,257,6] 13 :=
  permutation_upper _ _ _ [96,12,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4724

theorem m7066_9 : Upper (D 3) (R 3) [96,144,160,257,9] 13 :=
  permutation_upper _ _ _ [96,5,257,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4489

theorem m7066_10 : Upper (D 3) (R 3) [96,144,160,257,10] 13 :=
  permutation_upper _ _ _ [96,12,130,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4729

theorem m7066_12 : Upper (D 3) (R 3) [96,144,160,257,12] 13 :=
  permutation_upper _ _ _ [96,12,160,257,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4761

theorem m7066_65 : Upper (D 3) (R 3) [96,144,160,257,65] 13 :=
  permutation_upper _ _ _ [96,33,130,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4817

theorem m7066_66 : Upper (D 3) (R 3) [96,144,160,257,66] 13 :=
  permutation_upper _ _ _ [96,36,130,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4876

theorem m7066_68 : Upper (D 3) (R 3) [96,144,160,257,68] 13 :=
  permutation_upper _ _ _ [96,36,192,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4905

theorem m7066_72 : Upper (D 3) (R 3) [96,144,160,257,72] 13 :=
  permutation_upper _ _ _ [96,36,257,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4915

def r7066 : Route 9 := (fun mask => (mask,id))

def c7066 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7066 : Upper (D 3) (R 3) [96,144,160,257] 13 := by
  apply FastRouting.sound _ _ [96,144,160,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r7066 c7066
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7066_3
  · exact m7066_5
  · exact m7066_6
  · exact m7066_9
  · exact m7066_10
  · exact m7066_12
  · exact m7066_65
  · exact m7066_66
  · exact m7066_68
  · exact m7066_72

theorem m7067_5 : Upper (D 3) (R 3) [96,144,160,258,5] 13 :=
  permutation_upper _ _ _ [96,5,160,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4468

theorem m7067_9 : Upper (D 3) (R 3) [96,144,160,258,9] 13 :=
  permutation_upper _ _ _ [96,5,264,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4532

theorem m7067_12 : Upper (D 3) (R 3) [96,144,160,258,12] 13 :=
  permutation_upper _ _ _ [96,12,160,272,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4768

theorem m7067_65 : Upper (D 3) (R 3) [96,144,160,258,65] 13 :=
  permutation_upper _ _ _ [96,33,130,192,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4818

theorem m7067_68 : Upper (D 3) (R 3) [96,144,160,258,68] 13 :=
  permutation_upper _ _ _ [96,36,192,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4906

theorem m7067_72 : Upper (D 3) (R 3) [96,144,160,258,72] 13 :=
  permutation_upper _ _ _ [96,36,264,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4923

def r7067 : Route 9 := (fun mask => (mask,id))

def c7067 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7067 : Upper (D 3) (R 3) [96,144,160,258] 13 := by
  apply FastRouting.sound _ _ [96,144,160,258] 13 (by decide) (choices 2) [5,9,12,65,68,72] r7067 c7067
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7067_5
  · exact m7067_9
  · exact m7067_12
  · exact m7067_65
  · exact m7067_68
  · exact m7067_72

theorem m7068_3 : Upper (D 3) (R 3) [96,144,160,260,3] 13 :=
  permutation_upper _ _ _ [96,5,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4369

theorem m7068_9 : Upper (D 3) (R 3) [96,144,160,260,9] 13 :=
  permutation_upper _ _ _ [96,5,264,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4541

theorem m7068_10 : Upper (D 3) (R 3) [96,144,160,260,10] 13 :=
  permutation_upper _ _ _ [96,12,130,272,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4733

theorem m7068_65 : Upper (D 3) (R 3) [96,144,160,260,65] 13 :=
  permutation_upper _ _ _ [96,33,130,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4819

theorem m7068_66 : Upper (D 3) (R 3) [96,144,160,260,66] 13 :=
  permutation_upper _ _ _ [96,36,130,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4877

theorem m7068_72 : Upper (D 3) (R 3) [96,144,160,260,72] 13 :=
  permutation_upper _ _ _ [96,36,264,192,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4928

def r7068 : Route 9 := (fun mask => (mask,id))

def c7068 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7068 : Upper (D 3) (R 3) [96,144,160,260] 13 := by
  apply FastRouting.sound _ _ [96,144,160,260] 13 (by decide) (choices 2) [3,9,10,65,66,72] r7068 c7068
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7068_3
  · exact m7068_9
  · exact m7068_10
  · exact m7068_65
  · exact m7068_66
  · exact m7068_72

theorem m7069_3 : Upper (D 3) (R 3) [96,144,160,320,3] 13 :=
  permutation_upper _ _ _ [96,5,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4370

theorem m7069_5 : Upper (D 3) (R 3) [96,144,160,320,5] 13 :=
  permutation_upper _ _ _ [96,5,160,130,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4469

theorem m7069_6 : Upper (D 3) (R 3) [96,144,160,320,6] 13 :=
  permutation_upper _ _ _ [96,12,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4725

theorem m7069_9 : Upper (D 3) (R 3) [96,144,160,320,9] 13 :=
  permutation_upper _ _ _ [96,5,288,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4552

theorem m7069_10 : Upper (D 3) (R 3) [96,144,160,320,10] 13 :=
  permutation_upper _ _ _ [96,12,130,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4735

theorem m7069_12 : Upper (D 3) (R 3) [96,144,160,320,12] 13 :=
  permutation_upper _ _ _ [96,12,160,320,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4771

def r7069 : Route 9 := (fun mask => (mask,id))

def c7069 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u7069 : Upper (D 3) (R 3) [96,144,160,320] 13 := by
  apply FastRouting.sound _ _ [96,144,160,320] 13 (by decide) (choices 2) [3,5,6,9,10,12] r7069 c7069
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7069_3
  · exact m7069_5
  · exact m7069_6
  · exact m7069_9
  · exact m7069_10
  · exact m7069_12

theorem m7070_3 : Upper (D 3) (R 3) [96,160,192,257,3] 13 :=
  permutation_upper _ _ _ [96,5,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4474

theorem m7070_5 : Upper (D 3) (R 3) [96,160,192,257,5] 13 :=
  permutation_upper _ _ _ [96,5,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4474

theorem m7070_6 : Upper (D 3) (R 3) [96,160,192,257,6] 13 :=
  permutation_upper _ _ _ [96,12,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4756

theorem m7070_9 : Upper (D 3) (R 3) [96,160,192,257,9] 13 :=
  permutation_upper _ _ _ [96,5,257,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4490

theorem m7070_10 : Upper (D 3) (R 3) [96,160,192,257,10] 13 :=
  permutation_upper _ _ _ [96,12,160,257,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4762

theorem m7070_12 : Upper (D 3) (R 3) [96,160,192,257,12] 13 :=
  permutation_upper _ _ _ [96,12,160,257,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4762

def r7070 : Route 9 := (fun mask => (mask,id))

def c7070 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u7070 : Upper (D 3) (R 3) [96,160,192,257] 13 := by
  apply FastRouting.sound _ _ [96,160,192,257] 13 (by decide) (choices 2) [3,5,6,9,10,12] r7070 c7070
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7070_3
  · exact m7070_5
  · exact m7070_6
  · exact m7070_9
  · exact m7070_10
  · exact m7070_12

theorem m7071_5 : Upper (D 3) (R 3) [96,160,192,258,5] 13 :=
  permutation_upper _ _ _ [96,5,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4476

theorem m7071_9 : Upper (D 3) (R 3) [96,160,192,258,9] 13 :=
  permutation_upper _ _ _ [96,5,264,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4542

theorem m7071_12 : Upper (D 3) (R 3) [96,160,192,258,12] 13 :=
  permutation_upper _ _ _ [96,12,160,272,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4769

def r7071 : Route 9 := (fun mask => (mask,id))

def c7071 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u7071 : Upper (D 3) (R 3) [96,160,192,258] 13 := by
  apply FastRouting.sound _ _ [96,160,192,258] 13 (by decide) (choices 2) [5,9,12] r7071 c7071
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m7071_5
  · exact m7071_9
  · exact m7071_12

theorem m7072_3 : Upper (D 3) (R 3) [96,160,192,272,3] 13 :=
  permutation_upper _ _ _ [96,5,160,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4475

theorem m7072_5 : Upper (D 3) (R 3) [96,160,192,272,5] 13 :=
  permutation_upper _ _ _ [96,5,160,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4475

theorem m7072_6 : Upper (D 3) (R 3) [96,160,192,272,6] 13 :=
  permutation_upper _ _ _ [96,12,160,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4757

theorem m7072_9 : Upper (D 3) (R 3) [96,160,192,272,9] 13 :=
  permutation_upper _ _ _ [96,5,258,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4506

theorem m7072_10 : Upper (D 3) (R 3) [96,160,192,272,10] 13 :=
  permutation_upper _ _ _ [96,12,160,258,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4764

theorem m7072_12 : Upper (D 3) (R 3) [96,160,192,272,12] 13 :=
  permutation_upper _ _ _ [96,12,160,258,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4764

def r7072 : Route 9 := (fun mask => (mask,id))

def c7072 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u7072 : Upper (D 3) (R 3) [96,160,192,272] 13 := by
  apply FastRouting.sound _ _ [96,160,192,272] 13 (by decide) (choices 2) [3,5,6,9,10,12] r7072 c7072
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7072_3
  · exact m7072_5
  · exact m7072_6
  · exact m7072_9
  · exact m7072_10
  · exact m7072_12

def r7073 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7073 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7073 : Upper (D 3) (R 3) [258,5,24,33] 13 := by
  apply FastRouting.sound _ _ [258,5,24,33] 13 (by decide) (choices 2) [33,65,96,192] r7073 c7073
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4940
  · exact u4941
  · exact u4942
  · exact u4943

theorem m7074_33 : Upper (D 3) (R 3) [258,5,24,96,33] 13 :=
  permutation_upper _ _ _ [258,5,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4942

theorem m7074_129 : Upper (D 3) (R 3) [258,5,24,96,129] 13 :=
  permutation_upper _ _ _ [258,5,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4943

def r7074 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7074 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7074 : Upper (D 3) (R 3) [258,5,24,96] 13 := by
  apply FastRouting.sound _ _ [258,5,24,96] 13 (by decide) (choices 2) [33,96,129,160] r7074 c7074
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m7074_33
  · exact u4944
  · exact m7074_129
  · exact u4945

def r7075 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7075 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7075 : Upper (D 3) (R 3) [258,5,40,17] 13 := by
  apply FastRouting.sound _ _ [258,5,40,17] 13 (by decide) (choices 2) [33,65,96,192] r7075 c7075
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4946
  · exact u4947
  · exact u4948
  · exact u4949

def b7076 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 259 7 44 41 209 241 209 209 465), lower := (rows 259 7 44 41 16 32 64 128 256), losses := [] }

theorem u7076 : Upper (D 3) (R 3) [258,5,40,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7076
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7077 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 451, targets := 32 }], pairs := [(0,5)], upper := (rows 259 7 44 56 209 225 193 193 449), lower := (rows 259 7 44 56 16 32 64 128 256), losses := [] }

theorem u7077 : Upper (D 3) (R 3) [258,5,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7077
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7078 : Route 9 := (fun mask => (mask,id))

def c7078 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7078 : Upper (D 3) (R 3) [258,5,40,65] 13 := by
  apply FastRouting.sound _ _ [258,5,40,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7078 c7078
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u4950
  · exact u4951
  · exact u4952
  · exact u4953
  · exact u4954
  · exact u4955

def r7079 : Route 9 := (fun mask => (mask,id))

def c7079 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7079 : Upper (D 3) (R 3) [258,5,40,80] 13 := by
  apply FastRouting.sound _ _ [258,5,40,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7079 c7079
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u4956
  · exact u4957
  · exact u4958
  · exact u4959
  · exact u4960
  · exact u4961

#print axioms u7079
end Delivery.IrregularNine14.P03
