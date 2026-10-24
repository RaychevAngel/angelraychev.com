import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0470
import IrregularNine14P06C0471
import IrregularNine14P06C0472
import IrregularNine14P06C0473
import IrregularNine14P06C0474

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40740 : PairBound 9 := { available := 99, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 26 388 13 115 99 99 227 355), lower := (rows 7 26 388 13 16 32 64 128 256), losses := [] }

theorem u40740 : Upper (D 6) (R 6) [6,24,384,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40740
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40741 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 388 14 113 97 97 225 353), lower := (rows 7 26 388 14 16 32 64 128 256), losses := [] }

theorem u40741 : Upper (D 6) (R 6) [6,24,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40741
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40742_3 : Upper (D 6) (R 6) [6,24,384,33,3] 13 :=
  permutation_upper _ _ _ [6,24,384,3,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28232

theorem m40742_5 : Upper (D 6) (R 6) [6,24,384,33,5] 13 :=
  permutation_upper _ _ _ [6,24,384,5,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28235

theorem m40742_6 : Upper (D 6) (R 6) [6,24,384,33,6] 13 :=
  permutation_upper _ _ _ [6,24,384,6,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28238

def r40742 : Route 9 := (fun mask => (mask,id))

def c40742 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40742 : Upper (D 6) (R 6) [6,24,384,33] 13 := by
  apply FastRouting.sound _ _ [6,24,384,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40742 c40742
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40742_3
  · exact m40742_5
  · exact m40742_6
  · exact u28240
  · exact u28241
  · exact u28242
  · exact u28243
  · exact u28244
  · exact u28245
  · exact u28246

theorem m40743_5 : Upper (D 6) (R 6) [6,24,384,34,5] 13 :=
  permutation_upper _ _ _ [6,24,384,5,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28236

theorem m40743_33 : Upper (D 6) (R 6) [6,24,384,34,33] 13 :=
  permutation_upper _ _ _ [6,24,384,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28241

theorem m40743_65 : Upper (D 6) (R 6) [6,24,384,34,65] 13 :=
  permutation_upper _ _ _ [6,24,384,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28244

def r40743 : Route 9 := (fun mask => (mask,id))

def c40743 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40743 : Upper (D 6) (R 6) [6,24,384,34] 13 := by
  apply FastRouting.sound _ _ [6,24,384,34] 13 (by decide) (choices 2) [5,33,36,65,68,96] r40743 c40743
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40743_5
  · exact m40743_33
  · exact u28247
  · exact m40743_65
  · exact u28248
  · exact u28249

theorem m40744_3 : Upper (D 6) (R 6) [6,24,384,36,3] 13 :=
  permutation_upper _ _ _ [6,24,384,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28233

theorem m40744_33 : Upper (D 6) (R 6) [6,24,384,36,33] 13 :=
  permutation_upper _ _ _ [6,24,384,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28242

theorem m40744_34 : Upper (D 6) (R 6) [6,24,384,36,34] 13 :=
  permutation_upper _ _ _ [6,24,384,34,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28247

theorem m40744_65 : Upper (D 6) (R 6) [6,24,384,36,65] 13 :=
  permutation_upper _ _ _ [6,24,384,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28245

theorem m40744_66 : Upper (D 6) (R 6) [6,24,384,36,66] 13 :=
  permutation_upper _ _ _ [6,24,384,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28248

def r40744 : Route 9 := (fun mask => (mask,id))

def c40744 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40744 : Upper (D 6) (R 6) [6,24,384,36] 13 := by
  apply FastRouting.sound _ _ [6,24,384,36] 13 (by decide) (choices 2) [3,33,34,65,66,96] r40744 c40744
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40744_3
  · exact m40744_33
  · exact m40744_34
  · exact m40744_65
  · exact m40744_66
  · exact u28250

theorem m40745_3 : Upper (D 6) (R 6) [6,24,384,96,3] 13 :=
  permutation_upper _ _ _ [6,24,384,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28234

theorem m40745_5 : Upper (D 6) (R 6) [6,24,384,96,5] 13 :=
  permutation_upper _ _ _ [6,24,384,5,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28237

theorem m40745_6 : Upper (D 6) (R 6) [6,24,384,96,6] 13 :=
  permutation_upper _ _ _ [6,24,384,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28239

theorem m40745_33 : Upper (D 6) (R 6) [6,24,384,96,33] 13 :=
  permutation_upper _ _ _ [6,24,384,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28246

theorem m40745_34 : Upper (D 6) (R 6) [6,24,384,96,34] 13 :=
  permutation_upper _ _ _ [6,24,384,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28249

theorem m40745_36 : Upper (D 6) (R 6) [6,24,384,96,36] 13 :=
  permutation_upper _ _ _ [6,24,384,36,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28250

def r40745 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c40745 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40745 : Upper (D 6) (R 6) [6,24,384,96] 13 := by
  apply FastRouting.sound _ _ [6,24,384,96] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r40745 c40745
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40745_3
  · exact m40745_5
  · exact m40745_6
  · exact m40745_33
  · exact m40745_34
  · exact m40745_36
  · exact u28251

def b40746 : PairBound 9 := { available := 504, camps := [{ cop := 3, region := 496, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 69 14 504 504 504 504 504), lower := (rows 7 35 69 14 16 32 64 128 256), losses := [] }

theorem u40746 : Upper (D 6) (R 6) [6,33,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40746
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40747 : Route 9 := (fun mask => match mask with | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40747 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u40747 : Upper (D 6) (R 6) [6,33,65,18] 13 := by
  apply FastRouting.sound _ _ [6,33,65,18] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192,384] r40747 c40747
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28257
  · exact u28258
  · exact u28259
  · exact u28260
  · exact u28261
  · exact u28262
  · exact u28263
  · exact u28264
  · exact u28265
  · exact u28266
  · exact u28267

def b40748 : PairBound 9 := { available := 476, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 69 42 476 508 476 476 476), lower := (rows 7 35 69 42 16 32 64 128 256), losses := [] }

theorem u40748 : Upper (D 6) (R 6) [6,33,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40748
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40749 : PairBound 9 := { available := 474, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 69 44 474 506 474 474 474), lower := (rows 7 35 69 44 16 32 64 128 256), losses := [] }

theorem u40749 : Upper (D 6) (R 6) [6,33,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40749
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40750_6 : Upper (D 6) (R 6) [6,33,65,48,6] 13 :=
  permutation_upper _ _ _ [6,33,65,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28252

theorem m40750_10 : Upper (D 6) (R 6) [6,33,65,48,10] 13 :=
  permutation_upper _ _ _ [6,33,65,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28259

theorem m40750_12 : Upper (D 6) (R 6) [6,33,65,48,12] 13 :=
  permutation_upper _ _ _ [6,33,65,18,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28261

theorem m40750_66 : Upper (D 6) (R 6) [6,33,65,48,66] 13 :=
  permutation_upper _ _ _ [6,33,65,36,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28273

theorem m40750_68 : Upper (D 6) (R 6) [6,33,65,48,68] 13 :=
  permutation_upper _ _ _ [6,33,65,34,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28268

def r40750 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40750 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 36 => 5 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u40750 : Upper (D 6) (R 6) [6,33,65,48] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48] 13 (by decide) (choices 2) [6,10,12,66,68,72,130,132,136,192,384] r40750 c40750
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40750_6
  · exact m40750_10
  · exact m40750_12
  · exact m40750_66
  · exact m40750_68
  · exact u28278
  · exact u28279
  · exact u28280
  · exact u28281
  · exact u28282
  · exact u28283

theorem m40751_6 : Upper (D 6) (R 6) [6,33,65,96,6] 13 :=
  permutation_upper _ _ _ [6,33,65,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28253

theorem m40751_10 : Upper (D 6) (R 6) [6,33,65,96,10] 13 :=
  permutation_upper _ _ _ [6,33,65,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28262

theorem m40751_12 : Upper (D 6) (R 6) [6,33,65,96,12] 13 :=
  permutation_upper _ _ _ [6,33,65,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28262

theorem m40751_132 : Upper (D 6) (R 6) [6,33,65,96,132] 13 :=
  permutation_upper _ _ _ [6,33,65,96,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28284

def r40751 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40751 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u40751 : Upper (D 6) (R 6) [6,33,65,96] 13 := by
  apply FastRouting.sound _ _ [6,33,65,96] 13 (by decide) (choices 2) [6,10,12,130,132,136,384] r40751 c40751
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40751_6
  · exact m40751_10
  · exact m40751_12
  · exact u28284
  · exact m40751_132
  · exact u28285
  · exact u28286

theorem m40752_12 : Upper (D 6) (R 6) [6,33,65,130,12] 13 :=
  permutation_upper _ _ _ [6,33,65,18,132] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28263

theorem m40752_36 : Upper (D 6) (R 6) [6,33,65,130,36] 13 :=
  permutation_upper _ _ _ [6,33,65,36,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28274

theorem m40752_40 : Upper (D 6) (R 6) [6,33,65,130,40] 13 :=
  permutation_upper _ _ _ [6,33,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28279

theorem m40752_68 : Upper (D 6) (R 6) [6,33,65,130,68] 13 :=
  permutation_upper _ _ _ [6,33,65,34,132] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28269

theorem m40752_72 : Upper (D 6) (R 6) [6,33,65,130,72] 13 :=
  permutation_upper _ _ _ [6,33,65,48,132] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28280

theorem m40752_96 : Upper (D 6) (R 6) [6,33,65,130,96] 13 :=
  permutation_upper _ _ _ [6,33,65,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28284

def r40752 : Route 9 := (fun mask => (mask,id))

def c40752 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40752 : Upper (D 6) (R 6) [6,33,65,130] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130] 13 (by decide) (choices 2) [12,36,40,68,72,96,260,264,288,320] r40752 c40752
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40752_12
  · exact m40752_36
  · exact m40752_40
  · exact m40752_68
  · exact m40752_72
  · exact m40752_96
  · exact u28287
  · exact u28288
  · exact u28289
  · exact u28290

theorem m40753_6 : Upper (D 6) (R 6) [6,33,65,144,6] 13 :=
  permutation_upper _ _ _ [6,33,65,6,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28254

theorem m40753_10 : Upper (D 6) (R 6) [6,33,65,144,10] 13 :=
  permutation_upper _ _ _ [6,33,65,18,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28264

theorem m40753_12 : Upper (D 6) (R 6) [6,33,65,144,12] 13 :=
  permutation_upper _ _ _ [6,33,65,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28264

theorem m40753_34 : Upper (D 6) (R 6) [6,33,65,144,34] 13 :=
  permutation_upper _ _ _ [6,33,65,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28270

theorem m40753_36 : Upper (D 6) (R 6) [6,33,65,144,36] 13 :=
  permutation_upper _ _ _ [6,33,65,36,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28275

theorem m40753_40 : Upper (D 6) (R 6) [6,33,65,144,40] 13 :=
  permutation_upper _ _ _ [6,33,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28281

theorem m40753_66 : Upper (D 6) (R 6) [6,33,65,144,66] 13 :=
  permutation_upper _ _ _ [6,33,65,36,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28275

theorem m40753_68 : Upper (D 6) (R 6) [6,33,65,144,68] 13 :=
  permutation_upper _ _ _ [6,33,65,34,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28270

theorem m40753_72 : Upper (D 6) (R 6) [6,33,65,144,72] 13 :=
  permutation_upper _ _ _ [6,33,65,48,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28281

theorem m40753_96 : Upper (D 6) (R 6) [6,33,65,144,96] 13 :=
  permutation_upper _ _ _ [6,33,65,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28285

theorem m40753_258 : Upper (D 6) (R 6) [6,33,65,144,258] 13 :=
  permutation_upper _ _ _ [6,33,65,130,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28288

theorem m40753_260 : Upper (D 6) (R 6) [6,33,65,144,260] 13 :=
  permutation_upper _ _ _ [6,33,65,130,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28288

theorem m40753_320 : Upper (D 6) (R 6) [6,33,65,144,320] 13 :=
  permutation_upper _ _ _ [6,33,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28292

def r40753 : Route 9 := (fun mask => (mask,id))

def c40753 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40753 : Upper (D 6) (R 6) [6,33,65,144] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96,258,260,264,288,320] r40753 c40753
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40753_6
  · exact m40753_10
  · exact m40753_12
  · exact m40753_34
  · exact m40753_36
  · exact m40753_40
  · exact m40753_66
  · exact m40753_68
  · exact m40753_72
  · exact m40753_96
  · exact m40753_258
  · exact m40753_260
  · exact u28291
  · exact u28292
  · exact m40753_320

theorem m40754_6 : Upper (D 6) (R 6) [6,33,65,160,6] 13 :=
  permutation_upper _ _ _ [6,33,65,6,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28255

theorem m40754_10 : Upper (D 6) (R 6) [6,33,65,160,10] 13 :=
  permutation_upper _ _ _ [6,33,65,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28265

theorem m40754_12 : Upper (D 6) (R 6) [6,33,65,160,12] 13 :=
  permutation_upper _ _ _ [6,33,65,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28266

theorem m40754_66 : Upper (D 6) (R 6) [6,33,65,160,66] 13 :=
  permutation_upper _ _ _ [6,33,65,36,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28276

theorem m40754_68 : Upper (D 6) (R 6) [6,33,65,160,68] 13 :=
  permutation_upper _ _ _ [6,33,65,34,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28271

theorem m40754_72 : Upper (D 6) (R 6) [6,33,65,160,72] 13 :=
  permutation_upper _ _ _ [6,33,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28282

theorem m40754_258 : Upper (D 6) (R 6) [6,33,65,160,258] 13 :=
  permutation_upper _ _ _ [6,33,65,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28289

theorem m40754_260 : Upper (D 6) (R 6) [6,33,65,160,260] 13 :=
  permutation_upper _ _ _ [6,33,65,130,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28290

theorem m40754_264 : Upper (D 6) (R 6) [6,33,65,160,264] 13 :=
  permutation_upper _ _ _ [6,33,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28292

def r40754 : Route 9 := (fun mask => (mask,id))

def c40754 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40754 : Upper (D 6) (R 6) [6,33,65,160] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160] 13 (by decide) (choices 2) [6,10,12,66,68,72,258,260,264,320] r40754 c40754
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40754_6
  · exact m40754_10
  · exact m40754_12
  · exact m40754_66
  · exact m40754_68
  · exact m40754_72
  · exact m40754_258
  · exact m40754_260
  · exact m40754_264
  · exact u28293

theorem m40755_6 : Upper (D 6) (R 6) [6,33,65,384,6] 13 :=
  permutation_upper _ _ _ [6,33,65,6,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28256

theorem m40755_10 : Upper (D 6) (R 6) [6,33,65,384,10] 13 :=
  permutation_upper _ _ _ [6,33,65,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28267

theorem m40755_12 : Upper (D 6) (R 6) [6,33,65,384,12] 13 :=
  permutation_upper _ _ _ [6,33,65,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28267

theorem m40755_34 : Upper (D 6) (R 6) [6,33,65,384,34] 13 :=
  permutation_upper _ _ _ [6,33,65,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28272

theorem m40755_36 : Upper (D 6) (R 6) [6,33,65,384,36] 13 :=
  permutation_upper _ _ _ [6,33,65,36,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28277

theorem m40755_40 : Upper (D 6) (R 6) [6,33,65,384,40] 13 :=
  permutation_upper _ _ _ [6,33,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28283

theorem m40755_66 : Upper (D 6) (R 6) [6,33,65,384,66] 13 :=
  permutation_upper _ _ _ [6,33,65,36,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28277

theorem m40755_68 : Upper (D 6) (R 6) [6,33,65,384,68] 13 :=
  permutation_upper _ _ _ [6,33,65,34,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28272

theorem m40755_72 : Upper (D 6) (R 6) [6,33,65,384,72] 13 :=
  permutation_upper _ _ _ [6,33,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28283

theorem m40755_96 : Upper (D 6) (R 6) [6,33,65,384,96] 13 :=
  permutation_upper _ _ _ [6,33,65,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28286

def r40755 : Route 9 := (fun mask => (mask,id))

def c40755 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40755 : Upper (D 6) (R 6) [6,33,65,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,384] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r40755 c40755
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40755_6
  · exact m40755_10
  · exact m40755_12
  · exact m40755_34
  · exact m40755_36
  · exact m40755_40
  · exact m40755_66
  · exact m40755_68
  · exact m40755_72
  · exact m40755_96

def b40756 : PairBound 9 := { available := 500, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 76 11 500 500 500 500 500), lower := (rows 7 35 76 11 16 32 64 128 256), losses := [] }

theorem u40756 : Upper (D 6) (R 6) [6,33,72,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40756
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40757 : PairBound 9 := { available := 498, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 76 13 498 498 498 498 498), lower := (rows 7 35 76 13 16 32 64 128 256), losses := [] }

theorem u40757 : Upper (D 6) (R 6) [6,33,72,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40757
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40758 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 498, targets := 4 },{ cop := 0, region := 8, targets := 32 }], pairs := [(1,2),(3,5),(4,2)], upper := (rows 7 35 76 14 497 497 497 497 497), lower := (rows 7 35 76 14 16 32 64 128 256), losses := [] }

theorem u40758 : Upper (D 6) (R 6) [6,33,72,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40758
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40759 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40759 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u40759 : Upper (D 6) (R 6) [6,33,72,17] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192,384] r40759 c40759
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28294
  · exact u28295
  · exact u28296
  · exact u28297
  · exact u28298
  · exact u28299
  · exact u28300
  · exact u28301
  · exact u28302
  · exact u28303
  · exact u28304

def r40760 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40760 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u40760 : Upper (D 6) (R 6) [6,33,72,18] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192,384] r40760 c40760
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28305
  · exact u28306
  · exact u28307
  · exact u28308
  · exact u28309
  · exact u28310
  · exact u28311
  · exact u28312
  · exact u28313
  · exact u28314
  · exact u28315

def r40761 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40761 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u40761 : Upper (D 6) (R 6) [6,33,72,20] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,384] r40761 c40761
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28316
  · exact u28317
  · exact u28318
  · exact u28319
  · exact u28320
  · exact u28321
  · exact u28322
  · exact u28323
  · exact u28324
  · exact u28325
  · exact u28326

def b40762 : PairBound 9 := { available := 470, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 76 41 470 502 470 470 470), lower := (rows 7 35 76 41 16 32 64 128 256), losses := [] }

theorem u40762 : Upper (D 6) (R 6) [6,33,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40762
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40763 : PairBound 9 := { available := 469, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 76 42 469 501 469 469 469), lower := (rows 7 35 76 42 16 32 64 128 256), losses := [] }

theorem u40763 : Upper (D 6) (R 6) [6,33,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40763
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40764 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 498, targets := 4 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 7 35 76 44 467 499 467 467 467), lower := (rows 7 35 76 44 16 32 64 128 256), losses := [] }

theorem u40764 : Upper (D 6) (R 6) [6,33,72,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40764
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40765 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c40765 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 10 => 3 | 34 => 5 | 12 => 3 | 36 => 5 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u40765 : Upper (D 6) (R 6) [6,33,72,48] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192,384] r40765 c40765
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28327
  · exact u28328
  · exact u28329
  · exact u28330
  · exact u28331
  · exact u28332
  · exact u28333
  · exact u28334
  · exact u28335
  · exact u28336
  · exact u28337

def b40766 : PairBound 9 := { available := 438, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 76 73 438 438 502 438 438), lower := (rows 7 35 76 73 16 32 64 128 256), losses := [] }

theorem u40766 : Upper (D 6) (R 6) [6,33,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40766
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40767 : PairBound 9 := { available := 437, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 76 74 437 437 501 437 437), lower := (rows 7 35 76 74 16 32 64 128 256), losses := [] }

theorem u40767 : Upper (D 6) (R 6) [6,33,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40767
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40768 : PairBound 9 := { available := 435, camps := [{ cop := 6, region := 12, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 35 76 76 435 435 499 435 435), lower := (rows 7 35 76 76 16 32 64 128 256), losses := [] }

theorem u40768 : Upper (D 6) (R 6) [6,33,72,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40768
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40769 : PairBound 9 := { available := 423, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 76 88 439 423 487 423 423), lower := (rows 7 35 76 88 16 32 64 128 256), losses := [] }

theorem u40769 : Upper (D 6) (R 6) [6,33,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40769
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40770 : PairBound 9 := { available := 407, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 76 104 407 439 471 407 407), lower := (rows 7 35 76 104 16 32 64 128 256), losses := [] }

theorem u40770 : Upper (D 6) (R 6) [6,33,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40770
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40771 : Route 9 := (fun mask => (mask,id))

def c40771 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40771 : Upper (D 6) (R 6) [6,33,72,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r40771 c40771
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28338
  · exact u28339
  · exact u28340
  · exact u28341
  · exact u28342
  · exact u28343
  · exact u28344
  · exact u28345
  · exact u28346
  · exact u28347

def r40772 : Route 9 := (fun mask => (mask,id))

def c40772 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40772 : Upper (D 6) (R 6) [6,33,72,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r40772 c40772
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28348
  · exact u28349
  · exact u28350
  · exact u28351
  · exact u28352
  · exact u28353
  · exact u28354
  · exact u28355
  · exact u28356
  · exact u28357

def r40773 : Route 9 := (fun mask => (mask,id))

def c40773 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40773 : Upper (D 6) (R 6) [6,33,72,132] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r40773 c40773
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28358
  · exact u28359
  · exact u28360
  · exact u28361
  · exact u28362
  · exact u28363
  · exact u28364
  · exact u28365
  · exact u28366
  · exact u28367

def r40774 : Route 9 := (fun mask => (mask,id))

def c40774 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40774 : Upper (D 6) (R 6) [6,33,72,144] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,257,258,260,288,320] r40774 c40774
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28368
  · exact u28369
  · exact u28370
  · exact u28371
  · exact u28372
  · exact u28373
  · exact u28374
  · exact u28375
  · exact u28376
  · exact u28377
  · exact u28378
  · exact u28379
  · exact u28380
  · exact u28381
  · exact u28382

def r40775 : Route 9 := (fun mask => (mask,id))

def c40775 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 3 | 36 => 5 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40775 : Upper (D 6) (R 6) [6,33,72,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,257,258,260,320] r40775 c40775
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28383
  · exact u28384
  · exact u28385
  · exact u28386
  · exact u28387
  · exact u28388
  · exact u28389
  · exact u28390
  · exact u28391
  · exact u28392

def b40776 : PairBound 9 := { available := 311, camps := [{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 76 200 311 311 375 439 311), lower := (rows 7 35 76 200 16 32 64 128 256), losses := [] }

theorem u40776 : Upper (D 6) (R 6) [6,33,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40776
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40777 : Route 9 := (fun mask => (mask,id))

def c40777 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40777 : Upper (D 6) (R 6) [6,33,72,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96] r40777 c40777
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28393
  · exact u28394
  · exact u28395
  · exact u28396
  · exact u28397
  · exact u28398
  · exact u28399
  · exact u28400
  · exact u28401
  · exact u28402

def b40778 : PairBound 9 := { available := 376, camps := [{ cop := 3, region := 368, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 14 376 376 376 504 376), lower := (rows 7 35 133 14 16 32 64 128 256), losses := [] }

theorem u40778 : Upper (D 6) (R 6) [6,33,129,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40778
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40779 : Route 9 := (fun mask => (mask,id))

def c40779 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40779 : Upper (D 6) (R 6) [6,33,129,18] 13 := by
  apply FastRouting.sound _ _ [6,33,129,18] 13 (by decide) (choices 2) [12,36,40,68,72,96,260,264,288,320] r40779 c40779
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28409
  · exact u28410
  · exact u28411
  · exact u28412
  · exact u28413
  · exact u28414
  · exact u28415
  · exact u28416
  · exact u28417
  · exact u28418

theorem m40780_10 : Upper (D 6) (R 6) [6,33,129,20,10] 13 :=
  permutation_upper _ _ _ [6,33,129,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28409

def r40780 : Route 9 := (fun mask => (mask,id))

def c40780 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40780 : Upper (D 6) (R 6) [6,33,129,20] 13 := by
  apply FastRouting.sound _ _ [6,33,129,20] 13 (by decide) (choices 2) [10,34,40,66,72,96,258,264,288,320] r40780 c40780
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40780_10
  · exact u28419
  · exact u28420
  · exact u28421
  · exact u28422
  · exact u28423
  · exact u28424
  · exact u28425
  · exact u28426
  · exact u28427

def b40781 : PairBound 9 := { available := 348, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 7 35 133 42 348 380 348 476 348), lower := (rows 7 35 133 42 16 32 64 128 256), losses := [] }

theorem u40781 : Upper (D 6) (R 6) [6,33,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40781
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40782 : PairBound 9 := { available := 346, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 3, region := 3, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 7 35 133 44 346 378 346 474 346), lower := (rows 7 35 133 44 16 32 64 128 256), losses := [] }

theorem u40782 : Upper (D 6) (R 6) [6,33,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40782
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40783_6 : Upper (D 6) (R 6) [6,33,129,48,6] 13 :=
  permutation_upper _ _ _ [6,33,129,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28403

theorem m40783_10 : Upper (D 6) (R 6) [6,33,129,48,10] 13 :=
  permutation_upper _ _ _ [6,33,129,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28411

theorem m40783_12 : Upper (D 6) (R 6) [6,33,129,48,12] 13 :=
  permutation_upper _ _ _ [6,33,129,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28420

def r40783 : Route 9 := (fun mask => (mask,id))

def c40783 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40783 : Upper (D 6) (R 6) [6,33,129,48] 13 := by
  apply FastRouting.sound _ _ [6,33,129,48] 13 (by decide) (choices 2) [6,10,12,66,68,72,258,260,264,320] r40783 c40783
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40783_6
  · exact m40783_10
  · exact m40783_12
  · exact u28438
  · exact u28439
  · exact u28440
  · exact u28441
  · exact u28442
  · exact u28443
  · exact u28444

theorem m40784_12 : Upper (D 6) (R 6) [6,33,129,66,12] 13 :=
  permutation_upper _ _ _ [6,33,129,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28421

theorem m40784_36 : Upper (D 6) (R 6) [6,33,129,66,36] 13 :=
  permutation_upper _ _ _ [6,33,129,36,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28433

theorem m40784_40 : Upper (D 6) (R 6) [6,33,129,66,40] 13 :=
  permutation_upper _ _ _ [6,33,129,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28438

def r40784 : Route 9 := (fun mask => (mask,id))

def c40784 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40784 : Upper (D 6) (R 6) [6,33,129,66] 13 := by
  apply FastRouting.sound _ _ [6,33,129,66] 13 (by decide) (choices 2) [12,36,40,68,72,96,260,264,288,320] r40784 c40784
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40784_12
  · exact m40784_36
  · exact m40784_40
  · exact u28445
  · exact u28446
  · exact u28447
  · exact u28448
  · exact u28449
  · exact u28450
  · exact u28451

theorem m40785_10 : Upper (D 6) (R 6) [6,33,129,68,10] 13 :=
  permutation_upper _ _ _ [6,33,129,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28412

theorem m40785_34 : Upper (D 6) (R 6) [6,33,129,68,34] 13 :=
  permutation_upper _ _ _ [6,33,129,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28428

theorem m40785_40 : Upper (D 6) (R 6) [6,33,129,68,40] 13 :=
  permutation_upper _ _ _ [6,33,129,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28439

theorem m40785_66 : Upper (D 6) (R 6) [6,33,129,68,66] 13 :=
  permutation_upper _ _ _ [6,33,129,66,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28445

def r40785 : Route 9 := (fun mask => (mask,id))

def c40785 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40785 : Upper (D 6) (R 6) [6,33,129,68] 13 := by
  apply FastRouting.sound _ _ [6,33,129,68] 13 (by decide) (choices 2) [10,34,40,66,72,96,258,264,288,320] r40785 c40785
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40785_10
  · exact m40785_34
  · exact m40785_40
  · exact m40785_66
  · exact u28452
  · exact u28453
  · exact u28454
  · exact u28455
  · exact u28456
  · exact u28457

theorem m40786_6 : Upper (D 6) (R 6) [6,33,129,80,6] 13 :=
  permutation_upper _ _ _ [6,33,129,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28404

theorem m40786_10 : Upper (D 6) (R 6) [6,33,129,80,10] 13 :=
  permutation_upper _ _ _ [6,33,129,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28413

theorem m40786_12 : Upper (D 6) (R 6) [6,33,129,80,12] 13 :=
  permutation_upper _ _ _ [6,33,129,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28422

theorem m40786_34 : Upper (D 6) (R 6) [6,33,129,80,34] 13 :=
  permutation_upper _ _ _ [6,33,129,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28429

theorem m40786_36 : Upper (D 6) (R 6) [6,33,129,80,36] 13 :=
  permutation_upper _ _ _ [6,33,129,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28434

theorem m40786_40 : Upper (D 6) (R 6) [6,33,129,80,40] 13 :=
  permutation_upper _ _ _ [6,33,129,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28440

theorem m40786_66 : Upper (D 6) (R 6) [6,33,129,80,66] 13 :=
  permutation_upper _ _ _ [6,33,129,66,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28446

theorem m40786_68 : Upper (D 6) (R 6) [6,33,129,80,68] 13 :=
  permutation_upper _ _ _ [6,33,129,68,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28452

def r40786 : Route 9 := (fun mask => (mask,id))

def c40786 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 132 => 7 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40786 : Upper (D 6) (R 6) [6,33,129,80] 13 := by
  apply FastRouting.sound _ _ [6,33,129,80] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96,258,260,264,288,320] r40786 c40786
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40786_6
  · exact m40786_10
  · exact m40786_12
  · exact m40786_34
  · exact m40786_36
  · exact m40786_40
  · exact m40786_66
  · exact m40786_68
  · exact u28458
  · exact u28459
  · exact u28460
  · exact u28461
  · exact u28462
  · exact u28463
  · exact u28464

theorem m40787_6 : Upper (D 6) (R 6) [6,33,129,96,6] 13 :=
  permutation_upper _ _ _ [6,33,129,6,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28405

theorem m40787_10 : Upper (D 6) (R 6) [6,33,129,96,10] 13 :=
  permutation_upper _ _ _ [6,33,129,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28414

theorem m40787_12 : Upper (D 6) (R 6) [6,33,129,96,12] 13 :=
  permutation_upper _ _ _ [6,33,129,20,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28423

theorem m40787_66 : Upper (D 6) (R 6) [6,33,129,96,66] 13 :=
  permutation_upper _ _ _ [6,33,129,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28447

theorem m40787_68 : Upper (D 6) (R 6) [6,33,129,96,68] 13 :=
  permutation_upper _ _ _ [6,33,129,68,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28453

theorem m40787_72 : Upper (D 6) (R 6) [6,33,129,96,72] 13 :=
  permutation_upper _ _ _ [6,33,129,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28459

def r40787 : Route 9 := (fun mask => (mask,id))

def c40787 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40787 : Upper (D 6) (R 6) [6,33,129,96] 13 := by
  apply FastRouting.sound _ _ [6,33,129,96] 13 (by decide) (choices 2) [6,10,12,66,68,72,258,260,264,320] r40787 c40787
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40787_6
  · exact m40787_10
  · exact m40787_12
  · exact m40787_66
  · exact m40787_68
  · exact m40787_72
  · exact u28465
  · exact u28466
  · exact u28467
  · exact u28468

theorem m40788_12 : Upper (D 6) (R 6) [6,33,129,258,12] 13 :=
  permutation_upper _ _ _ [6,33,129,20,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28424

theorem m40788_36 : Upper (D 6) (R 6) [6,33,129,258,36] 13 :=
  permutation_upper _ _ _ [6,33,129,36,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28435

theorem m40788_40 : Upper (D 6) (R 6) [6,33,129,258,40] 13 :=
  permutation_upper _ _ _ [6,33,129,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28441

theorem m40788_68 : Upper (D 6) (R 6) [6,33,129,258,68] 13 :=
  permutation_upper _ _ _ [6,33,129,68,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28454

theorem m40788_72 : Upper (D 6) (R 6) [6,33,129,258,72] 13 :=
  permutation_upper _ _ _ [6,33,129,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28460

theorem m40788_96 : Upper (D 6) (R 6) [6,33,129,258,96] 13 :=
  permutation_upper _ _ _ [6,33,129,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28465

def r40788 : Route 9 := (fun mask => (mask,id))

def c40788 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40788 : Upper (D 6) (R 6) [6,33,129,258] 13 := by
  apply FastRouting.sound _ _ [6,33,129,258] 13 (by decide) (choices 2) [12,36,40,68,72,96] r40788 c40788
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40788_12
  · exact m40788_36
  · exact m40788_40
  · exact m40788_68
  · exact m40788_72
  · exact m40788_96

theorem m40789_10 : Upper (D 6) (R 6) [6,33,129,260,10] 13 :=
  permutation_upper _ _ _ [6,33,129,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28415

theorem m40789_34 : Upper (D 6) (R 6) [6,33,129,260,34] 13 :=
  permutation_upper _ _ _ [6,33,129,34,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28430

theorem m40789_40 : Upper (D 6) (R 6) [6,33,129,260,40] 13 :=
  permutation_upper _ _ _ [6,33,129,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28442

theorem m40789_66 : Upper (D 6) (R 6) [6,33,129,260,66] 13 :=
  permutation_upper _ _ _ [6,33,129,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28448

theorem m40789_72 : Upper (D 6) (R 6) [6,33,129,260,72] 13 :=
  permutation_upper _ _ _ [6,33,129,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28461

theorem m40789_96 : Upper (D 6) (R 6) [6,33,129,260,96] 13 :=
  permutation_upper _ _ _ [6,33,129,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28466

def r40789 : Route 9 := (fun mask => (mask,id))

def c40789 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40789 : Upper (D 6) (R 6) [6,33,129,260] 13 := by
  apply FastRouting.sound _ _ [6,33,129,260] 13 (by decide) (choices 2) [10,34,40,66,72,96] r40789 c40789
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40789_10
  · exact m40789_34
  · exact m40789_40
  · exact m40789_66
  · exact m40789_72
  · exact m40789_96

theorem m40790_6 : Upper (D 6) (R 6) [6,33,129,272,6] 13 :=
  permutation_upper _ _ _ [6,33,129,6,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28406

theorem m40790_10 : Upper (D 6) (R 6) [6,33,129,272,10] 13 :=
  permutation_upper _ _ _ [6,33,129,18,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28416

theorem m40790_12 : Upper (D 6) (R 6) [6,33,129,272,12] 13 :=
  permutation_upper _ _ _ [6,33,129,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28425

theorem m40790_34 : Upper (D 6) (R 6) [6,33,129,272,34] 13 :=
  permutation_upper _ _ _ [6,33,129,34,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28431

theorem m40790_36 : Upper (D 6) (R 6) [6,33,129,272,36] 13 :=
  permutation_upper _ _ _ [6,33,129,36,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28436

theorem m40790_40 : Upper (D 6) (R 6) [6,33,129,272,40] 13 :=
  permutation_upper _ _ _ [6,33,129,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28443

theorem m40790_66 : Upper (D 6) (R 6) [6,33,129,272,66] 13 :=
  permutation_upper _ _ _ [6,33,129,66,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28449

theorem m40790_68 : Upper (D 6) (R 6) [6,33,129,272,68] 13 :=
  permutation_upper _ _ _ [6,33,129,68,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28455

theorem m40790_72 : Upper (D 6) (R 6) [6,33,129,272,72] 13 :=
  permutation_upper _ _ _ [6,33,129,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28462

theorem m40790_96 : Upper (D 6) (R 6) [6,33,129,272,96] 13 :=
  permutation_upper _ _ _ [6,33,129,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28467

def r40790 : Route 9 := (fun mask => (mask,id))

def c40790 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40790 : Upper (D 6) (R 6) [6,33,129,272] 13 := by
  apply FastRouting.sound _ _ [6,33,129,272] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r40790 c40790
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40790_6
  · exact m40790_10
  · exact m40790_12
  · exact m40790_34
  · exact m40790_36
  · exact m40790_40
  · exact m40790_66
  · exact m40790_68
  · exact m40790_72
  · exact m40790_96

theorem m40791_6 : Upper (D 6) (R 6) [6,33,129,288,6] 13 :=
  permutation_upper _ _ _ [6,33,129,6,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28407

theorem m40791_10 : Upper (D 6) (R 6) [6,33,129,288,10] 13 :=
  permutation_upper _ _ _ [6,33,129,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28417

theorem m40791_12 : Upper (D 6) (R 6) [6,33,129,288,12] 13 :=
  permutation_upper _ _ _ [6,33,129,20,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28426

theorem m40791_66 : Upper (D 6) (R 6) [6,33,129,288,66] 13 :=
  permutation_upper _ _ _ [6,33,129,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28450

theorem m40791_68 : Upper (D 6) (R 6) [6,33,129,288,68] 13 :=
  permutation_upper _ _ _ [6,33,129,68,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28456

theorem m40791_72 : Upper (D 6) (R 6) [6,33,129,288,72] 13 :=
  permutation_upper _ _ _ [6,33,129,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28463

def r40791 : Route 9 := (fun mask => (mask,id))

def c40791 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40791 : Upper (D 6) (R 6) [6,33,129,288] 13 := by
  apply FastRouting.sound _ _ [6,33,129,288] 13 (by decide) (choices 2) [6,10,12,66,68,72] r40791 c40791
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40791_6
  · exact m40791_10
  · exact m40791_12
  · exact m40791_66
  · exact m40791_68
  · exact m40791_72

theorem m40792_6 : Upper (D 6) (R 6) [6,33,129,320,6] 13 :=
  permutation_upper _ _ _ [6,33,129,6,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28408

theorem m40792_10 : Upper (D 6) (R 6) [6,33,129,320,10] 13 :=
  permutation_upper _ _ _ [6,33,129,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28418

theorem m40792_12 : Upper (D 6) (R 6) [6,33,129,320,12] 13 :=
  permutation_upper _ _ _ [6,33,129,20,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28427

theorem m40792_34 : Upper (D 6) (R 6) [6,33,129,320,34] 13 :=
  permutation_upper _ _ _ [6,33,129,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28432

theorem m40792_36 : Upper (D 6) (R 6) [6,33,129,320,36] 13 :=
  permutation_upper _ _ _ [6,33,129,36,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28437

theorem m40792_40 : Upper (D 6) (R 6) [6,33,129,320,40] 13 :=
  permutation_upper _ _ _ [6,33,129,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28444

theorem m40792_66 : Upper (D 6) (R 6) [6,33,129,320,66] 13 :=
  permutation_upper _ _ _ [6,33,129,66,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28451

theorem m40792_68 : Upper (D 6) (R 6) [6,33,129,320,68] 13 :=
  permutation_upper _ _ _ [6,33,129,68,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28457

theorem m40792_72 : Upper (D 6) (R 6) [6,33,129,320,72] 13 :=
  permutation_upper _ _ _ [6,33,129,80,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28464

theorem m40792_96 : Upper (D 6) (R 6) [6,33,129,320,96] 13 :=
  permutation_upper _ _ _ [6,33,129,96,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u28468

def r40792 : Route 9 := (fun mask => (mask,id))

def c40792 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u40792 : Upper (D 6) (R 6) [6,33,129,320] 13 := by
  apply FastRouting.sound _ _ [6,33,129,320] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96] r40792 c40792
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m40792_6
  · exact m40792_10
  · exact m40792_12
  · exact m40792_34
  · exact m40792_36
  · exact m40792_40
  · exact m40792_66
  · exact m40792_68
  · exact m40792_72
  · exact m40792_96

def b40793 : PairBound 9 := { available := 372, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 140 11 372 372 372 500 372), lower := (rows 7 35 140 11 16 32 64 128 256), losses := [] }

theorem u40793 : Upper (D 6) (R 6) [6,33,136,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40793
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40794 : PairBound 9 := { available := 370, camps := [{ cop := 0, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 7 35 140 13 370 370 370 498 370), lower := (rows 7 35 140 13 16 32 64 128 256), losses := [] }

theorem u40794 : Upper (D 6) (R 6) [6,33,136,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40794
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40795 : PairBound 9 := { available := 369, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 0, region := 8, targets := 32 }], pairs := [(1,2),(3,5),(4,2)], upper := (rows 7 35 140 14 369 369 369 497 369), lower := (rows 7 35 140 14 16 32 64 128 256), losses := [] }

theorem u40795 : Upper (D 6) (R 6) [6,33,136,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40795
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40796 : Route 9 := (fun mask => (mask,id))

def c40796 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40796 : Upper (D 6) (R 6) [6,33,136,17] 13 := by
  apply FastRouting.sound _ _ [6,33,136,17] 13 (by decide) (choices 2) [6,34,36,66,68,96,258,260,288,320] r40796 c40796
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28469
  · exact u28470
  · exact u28471
  · exact u28472
  · exact u28473
  · exact u28474
  · exact u28475
  · exact u28476
  · exact u28477
  · exact u28478

def r40797 : Route 9 := (fun mask => (mask,id))

def c40797 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 132 => 7 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40797 : Upper (D 6) (R 6) [6,33,136,18] 13 := by
  apply FastRouting.sound _ _ [6,33,136,18] 13 (by decide) (choices 2) [5,33,36,65,68,96,257,260,288,320] r40797 c40797
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28479
  · exact u28480
  · exact u28481
  · exact u28482
  · exact u28483
  · exact u28484
  · exact u28485
  · exact u28486
  · exact u28487
  · exact u28488

def r40798 : Route 9 := (fun mask => (mask,id))

def c40798 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 6 => 2 | 10 => 3 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u40798 : Upper (D 6) (R 6) [6,33,136,20] 13 := by
  apply FastRouting.sound _ _ [6,33,136,20] 13 (by decide) (choices 2) [3,33,34,65,66,96,257,258,288,320] r40798 c40798
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u28489
  · exact u28490
  · exact u28491
  · exact u28492
  · exact u28493
  · exact u28494
  · exact u28495
  · exact u28496
  · exact u28497
  · exact u28498

def b40799 : PairBound 9 := { available := 342, camps := [{ cop := 1, region := 8, targets := 68 },{ cop := 3, region := 2, targets := 4 }], pairs := [(1,2),(3,2),(3,6)], upper := (rows 7 35 140 41 342 374 342 470 342), lower := (rows 7 35 140 41 16 32 64 128 256), losses := [] }

theorem u40799 : Upper (D 6) (R 6) [6,33,136,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b40799
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u40799
end Delivery.IrregularNine14.P06
