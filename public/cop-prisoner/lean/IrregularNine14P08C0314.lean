import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0119
import IrregularNine14P08C0120
import IrregularNine14P08C0121
import IrregularNine14P08C0122
import IrregularNine14P08C0123

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m18840_33 : Upper (D 8) (R 8) [6,24,96,160,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7194

theorem m18840_65 : Upper (D 8) (R 8) [6,24,96,160,65] 13 :=
  permutation_upper _ _ _ [6,24,96,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7201

theorem m18840_96 : Upper (D 8) (R 8) [6,24,96,160,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7206

theorem m18840_129 : Upper (D 8) (R 8) [6,24,96,160,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7211

def r18840 : Route 9 := (fun mask => (mask,id))

def c18840 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18840 : Upper (D 8) (R 8) [6,24,96,160] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18840 c18840
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18840_33
  · exact m18840_65
  · exact m18840_96
  · exact m18840_129
  · exact u7217
  · exact u7218
  · exact u7219
  · exact u7220
  · exact u7221
  · exact u7222

def b18841 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 100 200 433 417 481 417 417), lower := (rows 7 26 100 200 16 32 64 128 256), losses := [] }

theorem u18841 : Upper (D 8) (R 8) [6,24,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18842_33 : Upper (D 8) (R 8) [6,24,96,257,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7196

theorem m18842_65 : Upper (D 8) (R 8) [6,24,96,257,65] 13 :=
  permutation_upper _ _ _ [6,24,96,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7202

theorem m18842_96 : Upper (D 8) (R 8) [6,24,96,257,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7207

theorem m18842_129 : Upper (D 8) (R 8) [6,24,96,257,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7213

theorem m18842_160 : Upper (D 8) (R 8) [6,24,96,257,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7219

theorem m18842_192 : Upper (D 8) (R 8) [6,24,96,257,192] 13 :=
  permutation_upper _ _ _ [6,24,96,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7223

def r18842 : Route 9 := (fun mask => (mask,id))

def c18842 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18842 : Upper (D 8) (R 8) [6,24,96,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18842 c18842
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18842_33
  · exact m18842_65
  · exact m18842_96
  · exact m18842_129
  · exact m18842_160
  · exact m18842_192

theorem m18843_33 : Upper (D 8) (R 8) [6,24,96,288,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7197

theorem m18843_65 : Upper (D 8) (R 8) [6,24,96,288,65] 13 :=
  permutation_upper _ _ _ [6,24,96,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7203

theorem m18843_96 : Upper (D 8) (R 8) [6,24,96,288,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7208

theorem m18843_129 : Upper (D 8) (R 8) [6,24,96,288,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7214

theorem m18843_160 : Upper (D 8) (R 8) [6,24,96,288,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7220

theorem m18843_192 : Upper (D 8) (R 8) [6,24,96,288,192] 13 :=
  permutation_upper _ _ _ [6,24,96,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7224

def r18843 : Route 9 := (fun mask => (mask,id))

def c18843 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18843 : Upper (D 8) (R 8) [6,24,96,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18843 c18843
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18843_33
  · exact m18843_65
  · exact m18843_96
  · exact m18843_129
  · exact m18843_160
  · exact m18843_192

def b18844 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 100 328 177 161 225 161 417), lower := (rows 7 26 100 328 16 32 64 128 256), losses := [] }

theorem u18844 : Upper (D 8) (R 8) [6,24,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18845_33 : Upper (D 8) (R 8) [6,24,96,384,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7199

theorem m18845_65 : Upper (D 8) (R 8) [6,24,96,384,65] 13 :=
  permutation_upper _ _ _ [6,24,96,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7204

theorem m18845_96 : Upper (D 8) (R 8) [6,24,96,384,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7209

theorem m18845_129 : Upper (D 8) (R 8) [6,24,96,384,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7216

theorem m18845_160 : Upper (D 8) (R 8) [6,24,96,384,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7222

theorem m18845_192 : Upper (D 8) (R 8) [6,24,96,384,192] 13 :=
  permutation_upper _ _ _ [6,24,96,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7225

def r18845 : Route 9 := (fun mask => (mask,id))

def c18845 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18845 : Upper (D 8) (R 8) [6,24,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18845 c18845
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18845_33
  · exact m18845_65
  · exact m18845_96
  · exact m18845_129
  · exact m18845_160
  · exact m18845_192

def r18846 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18846 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18846 : Upper (D 8) (R 8) [6,24,192,33] 13 := by
  apply FastRouting.sound _ _ [6,24,192,33] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r18846 c18846
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7226
  · exact u7227
  · exact u7228
  · exact u7229
  · exact u7230
  · exact u7231
  · exact u7232

def b18847 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 196 73 433 417 481 417 417), lower := (rows 7 26 196 73 16 32 64 128 256), losses := [] }

theorem u18847 : Upper (D 8) (R 8) [6,24,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18848 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 196 104 433 417 481 417 417), lower := (rows 7 26 196 104 16 32 64 128 256), losses := [] }

theorem u18848 : Upper (D 8) (R 8) [6,24,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18849 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 26 196 200 305 289 353 417 289), lower := (rows 7 26 196 200 16 32 64 128 256), losses := [] }

theorem u18849 : Upper (D 8) (R 8) [6,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18850_33 : Upper (D 8) (R 8) [6,24,192,257,33] 13 :=
  permutation_upper _ _ _ [6,24,192,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7230

theorem m18850_65 : Upper (D 8) (R 8) [6,24,192,257,65] 13 :=
  permutation_upper _ _ _ [6,24,192,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7233

theorem m18850_96 : Upper (D 8) (R 8) [6,24,192,257,96] 13 :=
  permutation_upper _ _ _ [6,24,192,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7235

theorem m18850_192 : Upper (D 8) (R 8) [6,24,192,257,192] 13 :=
  permutation_upper _ _ _ [6,24,192,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7237

def r18850 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18850 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18850 : Upper (D 8) (R 8) [6,24,192,257] 13 := by
  apply FastRouting.sound _ _ [6,24,192,257] 13 (by decide) (choices 2) [33,65,96,192] r18850 c18850
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m18850_33
  · exact m18850_65
  · exact m18850_96
  · exact m18850_192

theorem m18851_33 : Upper (D 8) (R 8) [6,24,192,288,33] 13 :=
  permutation_upper _ _ _ [6,24,192,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7231

theorem m18851_65 : Upper (D 8) (R 8) [6,24,192,288,65] 13 :=
  permutation_upper _ _ _ [6,24,192,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7234

theorem m18851_96 : Upper (D 8) (R 8) [6,24,192,288,96] 13 :=
  permutation_upper _ _ _ [6,24,192,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7236

theorem m18851_192 : Upper (D 8) (R 8) [6,24,192,288,192] 13 :=
  permutation_upper _ _ _ [6,24,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7238

def r18851 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18851 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18851 : Upper (D 8) (R 8) [6,24,192,288] 13 := by
  apply FastRouting.sound _ _ [6,24,192,288] 13 (by decide) (choices 2) [33,65,96,192] r18851 c18851
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m18851_33
  · exact m18851_65
  · exact m18851_96
  · exact m18851_192

def b18852 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 196 328 177 161 225 161 417), lower := (rows 7 26 196 328 16 32 64 128 256), losses := [] }

theorem u18852 : Upper (D 8) (R 8) [6,24,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18853 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 261 41 240 224 224 224 480), lower := (rows 7 26 261 41 16 32 64 128 256), losses := [] }

theorem u18853 : Upper (D 8) (R 8) [6,24,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18854 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 261 73 240 224 224 224 480), lower := (rows 7 26 261 73 16 32 64 128 256), losses := [] }

theorem u18854 : Upper (D 8) (R 8) [6,24,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18855_33 : Upper (D 8) (R 8) [6,24,257,96,33] 13 :=
  permutation_upper _ _ _ [6,24,257,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7239

theorem m18855_65 : Upper (D 8) (R 8) [6,24,257,96,65] 13 :=
  permutation_upper _ _ _ [6,24,257,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7241

theorem m18855_129 : Upper (D 8) (R 8) [6,24,257,96,129] 13 :=
  permutation_upper _ _ _ [6,24,257,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7242

def r18855 : Route 9 := (fun mask => (mask,id))

def c18855 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18855 : Upper (D 8) (R 8) [6,24,257,96] 13 := by
  apply FastRouting.sound _ _ [6,24,257,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18855 c18855
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18855_33
  · exact m18855_65
  · exact u7244
  · exact m18855_129
  · exact u7245
  · exact u7246

theorem m18856_33 : Upper (D 8) (R 8) [6,24,257,192,33] 13 :=
  permutation_upper _ _ _ [6,24,257,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7240

theorem m18856_65 : Upper (D 8) (R 8) [6,24,257,192,65] 13 :=
  permutation_upper _ _ _ [6,24,257,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7243

theorem m18856_96 : Upper (D 8) (R 8) [6,24,257,192,96] 13 :=
  permutation_upper _ _ _ [6,24,257,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7246

def r18856 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18856 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18856 : Upper (D 8) (R 8) [6,24,257,192] 13 := by
  apply FastRouting.sound _ _ [6,24,257,192] 13 (by decide) (choices 2) [33,65,96,192] r18856 c18856
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m18856_33
  · exact m18856_65
  · exact m18856_96
  · exact u7247

def r18857 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18857 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18857 : Upper (D 8) (R 8) [6,24,288,33] 13 := by
  apply FastRouting.sound _ _ [6,24,288,33] 13 (by decide) (choices 2) [33,65,96,192] r18857 c18857
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7248
  · exact u7249
  · exact u7250
  · exact u7251

theorem m18858_33 : Upper (D 8) (R 8) [6,24,288,65,33] 13 :=
  permutation_upper _ _ _ [6,24,288,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7249

def r18858 : Route 9 := (fun mask => (mask,id))

def c18858 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18858 : Upper (D 8) (R 8) [6,24,288,65] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18858 c18858
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18858_33
  · exact u7252
  · exact u7253
  · exact u7254
  · exact u7255
  · exact u7256

theorem m18859_33 : Upper (D 8) (R 8) [6,24,288,96,33] 13 :=
  permutation_upper _ _ _ [6,24,288,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7250

theorem m18859_65 : Upper (D 8) (R 8) [6,24,288,96,65] 13 :=
  permutation_upper _ _ _ [6,24,288,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7253

theorem m18859_129 : Upper (D 8) (R 8) [6,24,288,96,129] 13 :=
  permutation_upper _ _ _ [6,24,288,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7255

def r18859 : Route 9 := (fun mask => (mask,id))

def c18859 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18859 : Upper (D 8) (R 8) [6,24,288,96] 13 := by
  apply FastRouting.sound _ _ [6,24,288,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18859 c18859
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18859_33
  · exact m18859_65
  · exact u7257
  · exact m18859_129
  · exact u7258
  · exact u7259

theorem m18860_33 : Upper (D 8) (R 8) [6,24,288,192,33] 13 :=
  permutation_upper _ _ _ [6,24,288,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7251

theorem m18860_65 : Upper (D 8) (R 8) [6,24,288,192,65] 13 :=
  permutation_upper _ _ _ [6,24,288,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7256

theorem m18860_96 : Upper (D 8) (R 8) [6,24,288,192,96] 13 :=
  permutation_upper _ _ _ [6,24,288,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7259

def r18860 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18860 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18860 : Upper (D 8) (R 8) [6,24,288,192] 13 := by
  apply FastRouting.sound _ _ [6,24,288,192] 13 (by decide) (choices 2) [33,65,96,192] r18860 c18860
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m18860_33
  · exact m18860_65
  · exact m18860_96
  · exact u7260

def r18861 : Route 9 := (fun mask => (mask,id))

def c18861 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18861 : Upper (D 8) (R 8) [6,24,320,33] 13 := by
  apply FastRouting.sound _ _ [6,24,320,33] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18861 c18861
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7261
  · exact u7262
  · exact u7263
  · exact u7264
  · exact u7265
  · exact u7266

def b18862 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 7 26 324 73 177 161 225 161 417), lower := (rows 7 26 324 73 16 32 64 128 256), losses := [] }

theorem u18862 : Upper (D 8) (R 8) [6,24,320,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18863 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 324 104 177 161 225 161 417), lower := (rows 7 26 324 104 16 32 64 128 256), losses := [] }

theorem u18863 : Upper (D 8) (R 8) [6,24,320,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18864_33 : Upper (D 8) (R 8) [6,24,320,129,33] 13 :=
  permutation_upper _ _ _ [6,24,320,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7264

theorem m18864_65 : Upper (D 8) (R 8) [6,24,320,129,65] 13 :=
  permutation_upper _ _ _ [6,24,320,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7267

theorem m18864_96 : Upper (D 8) (R 8) [6,24,320,129,96] 13 :=
  permutation_upper _ _ _ [6,24,320,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7269

def r18864 : Route 9 := (fun mask => (mask,id))

def c18864 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18864 : Upper (D 8) (R 8) [6,24,320,129] 13 := by
  apply FastRouting.sound _ _ [6,24,320,129] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18864 c18864
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18864_33
  · exact m18864_65
  · exact m18864_96
  · exact u7271
  · exact u7272
  · exact u7273

theorem m18865_33 : Upper (D 8) (R 8) [6,24,320,160,33] 13 :=
  permutation_upper _ _ _ [6,24,320,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7265

theorem m18865_65 : Upper (D 8) (R 8) [6,24,320,160,65] 13 :=
  permutation_upper _ _ _ [6,24,320,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7268

theorem m18865_96 : Upper (D 8) (R 8) [6,24,320,160,96] 13 :=
  permutation_upper _ _ _ [6,24,320,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7270

theorem m18865_129 : Upper (D 8) (R 8) [6,24,320,160,129] 13 :=
  permutation_upper _ _ _ [6,24,320,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7272

def r18865 : Route 9 := (fun mask => (mask,id))

def c18865 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18865 : Upper (D 8) (R 8) [6,24,320,160] 13 := by
  apply FastRouting.sound _ _ [6,24,320,160] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18865 c18865
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18865_33
  · exact m18865_65
  · exact m18865_96
  · exact m18865_129
  · exact u7274
  · exact u7275

def b18866 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 7 26 324 200 177 161 225 161 417), lower := (rows 7 26 324 200 16 32 64 128 256), losses := [] }

theorem u18866 : Upper (D 8) (R 8) [6,24,320,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18867 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 25 496 480 480 480 480), lower := (rows 7 35 76 25 16 32 64 128 256), losses := [] }

theorem u18867 : Upper (D 8) (R 8) [6,33,72,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18868 : PairBound 9 := { available := 496, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 76 41 496 496 496 496 496), lower := (rows 7 35 76 41 16 32 64 128 256), losses := [] }

theorem u18868 : Upper (D 8) (R 8) [6,33,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18869 : Route 9 := (fun mask => (mask,id))

def c18869 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18869 : Upper (D 8) (R 8) [6,33,72,48] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18869 c18869
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7276
  · exact u7277
  · exact u7278
  · exact u7279
  · exact u7280
  · exact u7281
  · exact u7282
  · exact u7283
  · exact u7284
  · exact u7285

def b18870 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 73 432 432 496 432 432), lower := (rows 7 35 76 73 16 32 64 128 256), losses := [] }

theorem u18870 : Upper (D 8) (R 8) [6,33,72,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18871 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 88 433 417 481 417 417), lower := (rows 7 35 76 88 16 32 64 128 256), losses := [] }

theorem u18871 : Upper (D 8) (R 8) [6,33,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18872 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 104 433 433 497 433 433), lower := (rows 7 35 76 104 16 32 64 128 256), losses := [] }

theorem u18872 : Upper (D 8) (R 8) [6,33,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18873 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 137 496 496 496 496 496), lower := (rows 7 35 76 137 16 32 64 128 256), losses := [] }

theorem u18873 : Upper (D 8) (R 8) [6,33,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18874 : Route 9 := (fun mask => (mask,id))

def c18874 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18874 : Upper (D 8) (R 8) [6,33,72,144] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18874 c18874
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7286
  · exact u7287
  · exact u7288
  · exact u7289
  · exact u7290
  · exact u7291
  · exact u7292
  · exact u7293
  · exact u7294
  · exact u7295

def r18875 : Route 9 := (fun mask => (mask,id))

def c18875 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u18875 : Upper (D 8) (R 8) [6,33,72,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r18875 c18875
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7296
  · exact u7297
  · exact u7298
  · exact u7299
  · exact u7300
  · exact u7301
  · exact u7302
  · exact u7303
  · exact u7304
  · exact u7305

def b18876 : PairBound 9 := { available := 433, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 200 433 433 497 433 433), lower := (rows 7 35 76 200 16 32 64 128 256), losses := [] }

theorem u18876 : Upper (D 8) (R 8) [6,33,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18877 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 265 240 240 240 240 496), lower := (rows 7 35 76 265 16 32 64 128 256), losses := [] }

theorem u18877 : Upper (D 8) (R 8) [6,33,72,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18878 : Route 9 := (fun mask => (mask,id))

def c18878 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18878 : Upper (D 8) (R 8) [6,33,72,272] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18878 c18878
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7306
  · exact u7307
  · exact u7308
  · exact u7309
  · exact u7310
  · exact u7311

def r18879 : Route 9 := (fun mask => (mask,id))

def c18879 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18879 : Upper (D 8) (R 8) [6,33,72,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18879 c18879
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7312
  · exact u7313
  · exact u7314
  · exact u7315
  · exact u7316
  · exact u7317

def b18880 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 179, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 328 177 177 241 177 433), lower := (rows 7 35 76 328 16 32 64 128 256), losses := [] }

theorem u18880 : Upper (D 8) (R 8) [6,33,72,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18881 : Route 9 := (fun mask => (mask,id))

def c18881 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18881 : Upper (D 8) (R 8) [6,33,72,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18881 c18881
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7318
  · exact u7319
  · exact u7320
  · exact u7321
  · exact u7322
  · exact u7323

def b18882 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 25 504 488 488 488 488), lower := (rows 7 35 196 25 16 32 64 128 256), losses := [] }

theorem u18882 : Upper (D 8) (R 8) [6,33,192,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18883 : PairBound 9 := { available := 504, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 41 504 504 504 504 504), lower := (rows 7 35 196 41 16 32 64 128 256), losses := [] }

theorem u18883 : Upper (D 8) (R 8) [6,33,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18884_9 : Upper (D 8) (R 8) [6,33,192,48,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7324

theorem m18884_33 : Upper (D 8) (R 8) [6,33,192,48,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7330

def r18884 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18884 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u18884 : Upper (D 8) (R 8) [6,33,192,48] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,192,257,264,288,320] r18884 c18884
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18884_9
  · exact m18884_33
  · exact u7336
  · exact u7337
  · exact u7338
  · exact u7339
  · exact u7340
  · exact u7341
  · exact u7342
  · exact u7343
  · exact u7344

def b18885 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 73 440 440 504 440 440), lower := (rows 7 35 196 73 16 32 64 128 256), losses := [] }

theorem u18885 : Upper (D 8) (R 8) [6,33,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18886_9 : Upper (D 8) (R 8) [6,33,192,80,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7325

theorem m18886_33 : Upper (D 8) (R 8) [6,33,192,80,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7331

theorem m18886_40 : Upper (D 8) (R 8) [6,33,192,80,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7338

theorem m18886_129 : Upper (D 8) (R 8) [6,33,192,80,129] 13 :=
  permutation_upper _ _ _ [6,33,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7345

def r18886 : Route 9 := (fun mask => (mask,id))

def c18886 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u18886 : Upper (D 8) (R 8) [6,33,192,80] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r18886 c18886
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18886_9
  · exact m18886_33
  · exact m18886_40
  · exact m18886_129
  · exact u7350
  · exact u7351
  · exact u7352
  · exact u7353
  · exact u7354
  · exact u7355

theorem m18887_9 : Upper (D 8) (R 8) [6,33,192,96,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7326

theorem m18887_33 : Upper (D 8) (R 8) [6,33,192,96,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7332

theorem m18887_40 : Upper (D 8) (R 8) [6,33,192,96,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7339

theorem m18887_129 : Upper (D 8) (R 8) [6,33,192,96,129] 13 :=
  permutation_upper _ _ _ [6,33,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7346

theorem m18887_136 : Upper (D 8) (R 8) [6,33,192,96,136] 13 :=
  permutation_upper _ _ _ [6,33,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7351

def r18887 : Route 9 := (fun mask => (mask,id))

def c18887 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u18887 : Upper (D 8) (R 8) [6,33,192,96] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r18887 c18887
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18887_9
  · exact m18887_33
  · exact m18887_40
  · exact m18887_129
  · exact m18887_136
  · exact u7356
  · exact u7357
  · exact u7358
  · exact u7359
  · exact u7360

def b18888 : PairBound 9 := { available := 313, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 200 313 313 377 441 313), lower := (rows 7 35 196 200 16 32 64 128 256), losses := [] }

theorem u18888 : Upper (D 8) (R 8) [6,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18889 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 265 248 248 248 248 504), lower := (rows 7 35 196 265 16 32 64 128 256), losses := [] }

theorem u18889 : Upper (D 8) (R 8) [6,33,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m18890_9 : Upper (D 8) (R 8) [6,33,192,272,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7327

theorem m18890_33 : Upper (D 8) (R 8) [6,33,192,272,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7333

theorem m18890_40 : Upper (D 8) (R 8) [6,33,192,272,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7342

theorem m18890_65 : Upper (D 8) (R 8) [6,33,192,272,65] 13 :=
  permutation_upper _ _ _ [6,33,192,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7347

theorem m18890_72 : Upper (D 8) (R 8) [6,33,192,272,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7353

theorem m18890_96 : Upper (D 8) (R 8) [6,33,192,272,96] 13 :=
  permutation_upper _ _ _ [6,33,192,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7358

theorem m18890_192 : Upper (D 8) (R 8) [6,33,192,272,192] 13 :=
  permutation_upper _ _ _ [6,33,192,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7361

def r18890 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18890 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18890 : Upper (D 8) (R 8) [6,33,192,272] 13 := by
  apply FastRouting.sound _ _ [6,33,192,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r18890 c18890
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18890_9
  · exact m18890_33
  · exact m18890_40
  · exact m18890_65
  · exact m18890_72
  · exact m18890_96
  · exact m18890_192

theorem m18891_9 : Upper (D 8) (R 8) [6,33,192,288,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7328

theorem m18891_33 : Upper (D 8) (R 8) [6,33,192,288,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7334

theorem m18891_40 : Upper (D 8) (R 8) [6,33,192,288,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7343

theorem m18891_65 : Upper (D 8) (R 8) [6,33,192,288,65] 13 :=
  permutation_upper _ _ _ [6,33,192,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7348

theorem m18891_72 : Upper (D 8) (R 8) [6,33,192,288,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7354

theorem m18891_96 : Upper (D 8) (R 8) [6,33,192,288,96] 13 :=
  permutation_upper _ _ _ [6,33,192,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7359

theorem m18891_192 : Upper (D 8) (R 8) [6,33,192,288,192] 13 :=
  permutation_upper _ _ _ [6,33,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7362

def r18891 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18891 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18891 : Upper (D 8) (R 8) [6,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r18891 c18891
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18891_9
  · exact m18891_33
  · exact m18891_40
  · exact m18891_65
  · exact m18891_72
  · exact m18891_96
  · exact m18891_192

theorem m18892_9 : Upper (D 8) (R 8) [6,33,192,320,9] 13 :=
  permutation_upper _ _ _ [6,33,192,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7329

theorem m18892_33 : Upper (D 8) (R 8) [6,33,192,320,33] 13 :=
  permutation_upper _ _ _ [6,33,192,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7335

theorem m18892_40 : Upper (D 8) (R 8) [6,33,192,320,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7344

theorem m18892_129 : Upper (D 8) (R 8) [6,33,192,320,129] 13 :=
  permutation_upper _ _ _ [6,33,192,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7349

theorem m18892_136 : Upper (D 8) (R 8) [6,33,192,320,136] 13 :=
  permutation_upper _ _ _ [6,33,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7355

theorem m18892_160 : Upper (D 8) (R 8) [6,33,192,320,160] 13 :=
  permutation_upper _ _ _ [6,33,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7360

def r18892 : Route 9 := (fun mask => (mask,id))

def c18892 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u18892 : Upper (D 8) (R 8) [6,33,192,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r18892 c18892
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m18892_9
  · exact m18892_33
  · exact m18892_40
  · exact m18892_129
  · exact m18892_136
  · exact m18892_160

def b18893 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 268 25 240 224 224 224 480), lower := (rows 7 35 268 25 16 32 64 128 256), losses := [] }

theorem u18893 : Upper (D 8) (R 8) [6,33,264,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18894 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 268 41 240 240 240 240 496), lower := (rows 7 35 268 41 16 32 64 128 256), losses := [] }

theorem u18894 : Upper (D 8) (R 8) [6,33,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18895 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18895 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18895 : Upper (D 8) (R 8) [6,33,264,48] 13 := by
  apply FastRouting.sound _ _ [6,33,264,48] 13 (by decide) (choices 2) [33,65,96,192] r18895 c18895
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7363
  · exact u7364
  · exact u7365
  · exact u7366

def b18896 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 268 73 240 240 240 240 496), lower := (rows 7 35 268 73 16 32 64 128 256), losses := [] }

theorem u18896 : Upper (D 8) (R 8) [6,33,264,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18897 : Route 9 := (fun mask => (mask,id))

def c18897 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18897 : Upper (D 8) (R 8) [6,33,264,80] 13 := by
  apply FastRouting.sound _ _ [6,33,264,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18897 c18897
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7367
  · exact u7368
  · exact u7369
  · exact u7370
  · exact u7371
  · exact u7372

def r18898 : Route 9 := (fun mask => (mask,id))

def c18898 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18898 : Upper (D 8) (R 8) [6,33,264,96] 13 := by
  apply FastRouting.sound _ _ [6,33,264,96] 13 (by decide) (choices 2) [33,65,96,129,160,192] r18898 c18898
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7373
  · exact u7374
  · exact u7375
  · exact u7376
  · exact u7377
  · exact u7378

def r18899 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c18899 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u18899 : Upper (D 8) (R 8) [6,33,264,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,192] 13 (by decide) (choices 2) [33,65,96,192] r18899 c18899
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u7379
  · exact u7380
  · exact u7381
  · exact u7382

#print axioms u18899
end Delivery.IrregularNine14.P08
