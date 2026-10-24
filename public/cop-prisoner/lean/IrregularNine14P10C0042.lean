import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0019
import IrregularNine14P10C0020
import IrregularNine14P10C0021
import IrregularNine14P10C0022

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2520 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 26 100 104 433 417 481 417 417), lower := (rows 7 26 100 104 16 32 64 128 256), losses := [] }

theorem u2520 : Upper (D 10) (R 10) [6,24,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2520 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2521_96 : Upper (D 10) (R 10) [6,24,96,129,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1173

def r2521 : Route 9 := (fun mask => (mask,id))

def c2521 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2521 : Upper (D 10) (R 10) [6,24,96,129] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2521 c2521
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2521_96
  · exact u1176
  · exact u1177
  · exact u1178
  · exact u1179
  · exact u1180

theorem m2522_33 : Upper (D 10) (R 10) [6,24,96,160,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1168

theorem m2522_65 : Upper (D 10) (R 10) [6,24,96,160,65] 13 :=
  permutation_upper _ _ _ [6,24,96,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1171

theorem m2522_96 : Upper (D 10) (R 10) [6,24,96,160,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1174

theorem m2522_129 : Upper (D 10) (R 10) [6,24,96,160,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1176

theorem m2522_257 : Upper (D 10) (R 10) [6,24,96,160,257] 13 :=
  permutation_upper _ _ _ [6,24,96,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1178

def r2522 : Route 9 := (fun mask => (mask,id))

def c2522 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2522 : Upper (D 10) (R 10) [6,24,96,160] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r2522 c2522
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2522_33
  · exact m2522_65
  · exact m2522_96
  · exact m2522_129
  · exact u1181
  · exact u1182
  · exact m2522_257
  · exact u1183
  · exact u1184
  · exact u1185

theorem m2523_33 : Upper (D 10) (R 10) [6,24,96,192,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1169

theorem m2523_129 : Upper (D 10) (R 10) [6,24,96,192,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1177

theorem m2523_160 : Upper (D 10) (R 10) [6,24,96,192,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1182

theorem m2523_257 : Upper (D 10) (R 10) [6,24,96,192,257] 13 :=
  permutation_upper _ _ _ [6,24,96,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1179

theorem m2523_288 : Upper (D 10) (R 10) [6,24,96,192,288] 13 :=
  permutation_upper _ _ _ [6,24,96,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1184

def r2523 : Route 9 := (fun mask => (mask,id))

def c2523 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2523 : Upper (D 10) (R 10) [6,24,96,192] 13 := by
  apply FastRouting.sound _ _ [6,24,96,192] 13 (by decide) (choices 2) [33,129,160,257,288,384] r2523 c2523
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2523_33
  · exact m2523_129
  · exact m2523_160
  · exact m2523_257
  · exact m2523_288
  · exact u1186

theorem m2524_33 : Upper (D 10) (R 10) [6,24,96,384,33] 13 :=
  permutation_upper _ _ _ [6,24,96,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1170

theorem m2524_65 : Upper (D 10) (R 10) [6,24,96,384,65] 13 :=
  permutation_upper _ _ _ [6,24,96,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1172

theorem m2524_96 : Upper (D 10) (R 10) [6,24,96,384,96] 13 :=
  permutation_upper _ _ _ [6,24,96,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1175

theorem m2524_129 : Upper (D 10) (R 10) [6,24,96,384,129] 13 :=
  permutation_upper _ _ _ [6,24,96,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1180

theorem m2524_160 : Upper (D 10) (R 10) [6,24,96,384,160] 13 :=
  permutation_upper _ _ _ [6,24,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1185

theorem m2524_192 : Upper (D 10) (R 10) [6,24,96,384,192] 13 :=
  permutation_upper _ _ _ [6,24,96,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1186

def r2524 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2524 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2524 : Upper (D 10) (R 10) [6,24,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,384] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r2524 c2524
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2524_33
  · exact m2524_65
  · exact m2524_96
  · exact m2524_129
  · exact m2524_160
  · exact m2524_192
  · exact u1187

def r2525 : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2525 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2525 : Upper (D 10) (R 10) [6,24,192,33] 13 := by
  apply FastRouting.sound _ _ [6,24,192,33] 13 (by decide) (choices 2) [96,192,288,320] r2525 c2525
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1188
  · exact u1189
  · exact u1190
  · exact u1191

def b2526 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 26 196 73 432 416 480 416 416), lower := (rows 7 26 196 73 16 32 64 128 256), losses := [] }

theorem u2526 : Upper (D 10) (R 10) [6,24,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2526 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2527_33 : Upper (D 10) (R 10) [6,24,192,96,33] 13 :=
  permutation_upper _ _ _ [6,24,192,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1188

theorem m2527_129 : Upper (D 10) (R 10) [6,24,192,96,129] 13 :=
  permutation_upper _ _ _ [6,24,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1192

def r2527 : Route 9 := (fun mask => (mask,id))

def c2527 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2527 : Upper (D 10) (R 10) [6,24,192,96] 13 := by
  apply FastRouting.sound _ _ [6,24,192,96] 13 (by decide) (choices 2) [33,129,160,257,288,384] r2527 c2527
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2527_33
  · exact m2527_129
  · exact u1195
  · exact u1196
  · exact u1197
  · exact u1198

def b2528 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 26 196 200 305 289 353 417 289), lower := (rows 7 26 196 200 16 32 64 128 256), losses := [] }

theorem u2528 : Upper (D 10) (R 10) [6,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2528 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2529_96 : Upper (D 10) (R 10) [6,24,192,257,96] 13 :=
  permutation_upper _ _ _ [6,24,192,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1196

theorem m2529_192 : Upper (D 10) (R 10) [6,24,192,257,192] 13 :=
  permutation_upper _ _ _ [6,24,192,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1199

def r2529 : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2529 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2529 : Upper (D 10) (R 10) [6,24,192,257] 13 := by
  apply FastRouting.sound _ _ [6,24,192,257] 13 (by decide) (choices 2) [96,192,288,320] r2529 c2529
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2529_96
  · exact m2529_192
  · exact u1201
  · exact u1202

theorem m2530_33 : Upper (D 10) (R 10) [6,24,192,288,33] 13 :=
  permutation_upper _ _ _ [6,24,192,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1190

theorem m2530_65 : Upper (D 10) (R 10) [6,24,192,288,65] 13 :=
  permutation_upper _ _ _ [6,24,192,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1193

theorem m2530_96 : Upper (D 10) (R 10) [6,24,192,288,96] 13 :=
  permutation_upper _ _ _ [6,24,192,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1197

theorem m2530_192 : Upper (D 10) (R 10) [6,24,192,288,192] 13 :=
  permutation_upper _ _ _ [6,24,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1200

theorem m2530_257 : Upper (D 10) (R 10) [6,24,192,288,257] 13 :=
  permutation_upper _ _ _ [6,24,192,257,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1201

def r2530 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2530 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2530 : Upper (D 10) (R 10) [6,24,192,288] 13 := by
  apply FastRouting.sound _ _ [6,24,192,288] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r2530 c2530
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2530_33
  · exact m2530_65
  · exact m2530_96
  · exact m2530_192
  · exact m2530_257
  · exact u1203
  · exact u1204

theorem m2531_33 : Upper (D 10) (R 10) [6,24,192,320,33] 13 :=
  permutation_upper _ _ _ [6,24,192,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1191

theorem m2531_129 : Upper (D 10) (R 10) [6,24,192,320,129] 13 :=
  permutation_upper _ _ _ [6,24,192,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1194

theorem m2531_160 : Upper (D 10) (R 10) [6,24,192,320,160] 13 :=
  permutation_upper _ _ _ [6,24,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1198

theorem m2531_257 : Upper (D 10) (R 10) [6,24,192,320,257] 13 :=
  permutation_upper _ _ _ [6,24,192,257,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1202

theorem m2531_288 : Upper (D 10) (R 10) [6,24,192,320,288] 13 :=
  permutation_upper _ _ _ [6,24,192,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1204

def r2531 : Route 9 := (fun mask => (mask,id))

def c2531 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2531 : Upper (D 10) (R 10) [6,24,192,320] 13 := by
  apply FastRouting.sound _ _ [6,24,192,320] 13 (by decide) (choices 2) [33,129,160,257,288,384] r2531 c2531
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2531_33
  · exact m2531_129
  · exact m2531_160
  · exact m2531_257
  · exact m2531_288
  · exact u1205

def b2532 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 44 104 464 496 464 464 464), lower := (rows 7 35 44 104 16 32 64 128 256), losses := [] }

theorem u2532 : Upper (D 10) (R 10) [6,33,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2532 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2533 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 44 200 496 496 496 496 496), lower := (rows 7 35 44 200 16 32 64 128 256), losses := [] }

theorem u2533 : Upper (D 10) (R 10) [6,33,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2533 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2534 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 52 104 472 488 456 456 456), lower := (rows 7 35 52 104 16 32 64 128 256), losses := [] }

theorem u2534 : Upper (D 10) (R 10) [6,33,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2534 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2535 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 52 200 504 488 488 488 488), lower := (rows 7 35 52 200 16 32 64 128 256), losses := [] }

theorem u2535 : Upper (D 10) (R 10) [6,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2535 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2536 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2536 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2536 : Upper (D 10) (R 10) [6,33,72,48] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48] 13 (by decide) (choices 2) [96,160,192,384] r2536 c2536
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1214
  · exact u1215
  · exact u1216
  · exact u1217

def b2537 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 88 432 416 480 416 416), lower := (rows 7 35 76 88 16 32 64 128 256), losses := [] }

theorem u2537 : Upper (D 10) (R 10) [6,33,72,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2537 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2538 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 76 104 432 432 496 432 432), lower := (rows 7 35 76 104 16 32 64 128 256), losses := [] }

theorem u2538 : Upper (D 10) (R 10) [6,33,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2538 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2539 : Route 9 := (fun mask => (mask,id))

def c2539 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2539 : Upper (D 10) (R 10) [6,33,72,144] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2539 c2539
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1222
  · exact u1223
  · exact u1224
  · exact u1225
  · exact u1226
  · exact u1227

def r2540 : Route 9 := (fun mask => (mask,id))

def c2540 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2540 : Upper (D 10) (R 10) [6,33,72,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2540 c2540
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1228
  · exact u1229
  · exact u1230
  · exact u1231
  · exact u1232
  · exact u1233

def b2541 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 200 432 432 496 432 432), lower := (rows 7 35 76 200 16 32 64 128 256), losses := [] }

theorem u2541 : Upper (D 10) (R 10) [6,33,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2541 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2542 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2542 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2542 : Upper (D 10) (R 10) [6,33,72,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384] 13 (by decide) (choices 2) [96,160,192,384] r2542 c2542
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1237
  · exact u1238
  · exact u1239
  · exact u1240

theorem m2543_40 : Upper (D 10) (R 10) [6,33,80,96,40] 13 :=
  permutation_upper _ _ _ [6,33,72,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1214

theorem m2543_136 : Upper (D 10) (R 10) [6,33,80,96,136] 13 :=
  permutation_upper _ _ _ [6,33,72,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1222

theorem m2543_160 : Upper (D 10) (R 10) [6,33,80,96,160] 13 :=
  permutation_upper _ _ _ [6,33,72,160,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1228

theorem m2543_384 : Upper (D 10) (R 10) [6,33,80,96,384] 13 :=
  permutation_upper _ _ _ [6,33,72,384,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1237

def r2543 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2543 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2543 : Upper (D 10) (R 10) [6,33,80,96] 13 := by
  apply FastRouting.sound _ _ [6,33,80,96] 13 (by decide) (choices 2) [40,136,160,384] r2543 c2543
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2543_40
  · exact m2543_136
  · exact m2543_160
  · exact m2543_384

theorem m2544_40 : Upper (D 10) (R 10) [6,33,80,160,40] 13 :=
  permutation_upper _ _ _ [6,33,72,48,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1215

theorem m2544_72 : Upper (D 10) (R 10) [6,33,80,160,72] 13 :=
  permutation_upper _ _ _ [6,33,72,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1218

theorem m2544_96 : Upper (D 10) (R 10) [6,33,80,160,96] 13 :=
  permutation_upper _ _ _ [6,33,72,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1220

theorem m2544_136 : Upper (D 10) (R 10) [6,33,80,160,136] 13 :=
  permutation_upper _ _ _ [6,33,72,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1223

theorem m2544_160 : Upper (D 10) (R 10) [6,33,80,160,160] 13 :=
  permutation_upper _ _ _ [6,33,72,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1229

theorem m2544_192 : Upper (D 10) (R 10) [6,33,80,160,192] 13 :=
  permutation_upper _ _ _ [6,33,72,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1234

theorem m2544_264 : Upper (D 10) (R 10) [6,33,80,160,264] 13 :=
  permutation_upper _ _ _ [6,33,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1225

theorem m2544_288 : Upper (D 10) (R 10) [6,33,80,160,288] 13 :=
  permutation_upper _ _ _ [6,33,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1231

theorem m2544_320 : Upper (D 10) (R 10) [6,33,80,160,320] 13 :=
  permutation_upper _ _ _ [6,33,72,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1235

theorem m2544_384 : Upper (D 10) (R 10) [6,33,80,160,384] 13 :=
  permutation_upper _ _ _ [6,33,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1238

def r2544 : Route 9 := (fun mask => (mask,id))

def c2544 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2544 : Upper (D 10) (R 10) [6,33,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,80,160] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2544 c2544
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2544_40
  · exact m2544_72
  · exact m2544_96
  · exact m2544_136
  · exact m2544_160
  · exact m2544_192
  · exact m2544_264
  · exact m2544_288
  · exact m2544_320
  · exact m2544_384

theorem m2545_40 : Upper (D 10) (R 10) [6,33,80,192,40] 13 :=
  permutation_upper _ _ _ [6,33,72,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1216

theorem m2545_136 : Upper (D 10) (R 10) [6,33,80,192,136] 13 :=
  permutation_upper _ _ _ [6,33,72,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1224

theorem m2545_160 : Upper (D 10) (R 10) [6,33,80,192,160] 13 :=
  permutation_upper _ _ _ [6,33,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1230

theorem m2545_264 : Upper (D 10) (R 10) [6,33,80,192,264] 13 :=
  permutation_upper _ _ _ [6,33,72,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1226

theorem m2545_288 : Upper (D 10) (R 10) [6,33,80,192,288] 13 :=
  permutation_upper _ _ _ [6,33,72,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1232

theorem m2545_384 : Upper (D 10) (R 10) [6,33,80,192,384] 13 :=
  permutation_upper _ _ _ [6,33,72,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1239

def r2545 : Route 9 := (fun mask => (mask,id))

def c2545 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2545 : Upper (D 10) (R 10) [6,33,80,192] 13 := by
  apply FastRouting.sound _ _ [6,33,80,192] 13 (by decide) (choices 2) [40,136,160,264,288,384] r2545 c2545
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2545_40
  · exact m2545_136
  · exact m2545_160
  · exact m2545_264
  · exact m2545_288
  · exact m2545_384

theorem m2546_40 : Upper (D 10) (R 10) [6,33,80,384,40] 13 :=
  permutation_upper _ _ _ [6,33,72,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1217

theorem m2546_72 : Upper (D 10) (R 10) [6,33,80,384,72] 13 :=
  permutation_upper _ _ _ [6,33,72,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1219

theorem m2546_96 : Upper (D 10) (R 10) [6,33,80,384,96] 13 :=
  permutation_upper _ _ _ [6,33,72,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1221

theorem m2546_136 : Upper (D 10) (R 10) [6,33,80,384,136] 13 :=
  permutation_upper _ _ _ [6,33,72,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1227

theorem m2546_160 : Upper (D 10) (R 10) [6,33,80,384,160] 13 :=
  permutation_upper _ _ _ [6,33,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1233

theorem m2546_192 : Upper (D 10) (R 10) [6,33,80,384,192] 13 :=
  permutation_upper _ _ _ [6,33,72,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1236

theorem m2546_384 : Upper (D 10) (R 10) [6,33,80,384,384] 13 :=
  permutation_upper _ _ _ [6,33,72,384,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1240

def r2546 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2546 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2546 : Upper (D 10) (R 10) [6,33,80,384] 13 := by
  apply FastRouting.sound _ _ [6,33,80,384] 13 (by decide) (choices 2) [40,72,96,136,160,192,384] r2546 c2546
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2546_40
  · exact m2546_72
  · exact m2546_96
  · exact m2546_136
  · exact m2546_160
  · exact m2546_192
  · exact m2546_384

def b2547 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 100 104 408 440 472 408 408), lower := (rows 7 35 100 104 16 32 64 128 256), losses := [] }

theorem u2547 : Upper (D 10) (R 10) [6,33,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2547 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2548 : PairBound 9 := { available := 472, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 168 472 504 472 472 472), lower := (rows 7 35 100 168 16 32 64 128 256), losses := [] }

theorem u2548 : Upper (D 10) (R 10) [6,33,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2548 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2549 : PairBound 9 := { available := 440, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 200 440 440 504 440 440), lower := (rows 7 35 100 200 16 32 64 128 256), losses := [] }

theorem u2549 : Upper (D 10) (R 10) [6,33,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2549 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2550 : PairBound 9 := { available := 504, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 392 504 504 504 504 504), lower := (rows 7 35 100 392 16 32 64 128 256), losses := [] }

theorem u2550 : Upper (D 10) (R 10) [6,33,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2550 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2551 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2551 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2551 : Upper (D 10) (R 10) [6,33,192,48] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48] 13 (by decide) (choices 2) [40,72,96,192,264,288,320] r2551 c2551
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1257
  · exact u1258
  · exact u1259
  · exact u1260
  · exact u1261
  · exact u1262
  · exact u1263

theorem m2552_40 : Upper (D 10) (R 10) [6,33,192,80,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1258

def r2552 : Route 9 := (fun mask => (mask,id))

def c2552 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2552 : Upper (D 10) (R 10) [6,33,192,80] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80] 13 (by decide) (choices 2) [40,136,160,264,288,384] r2552 c2552
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2552_40
  · exact u1264
  · exact u1265
  · exact u1266
  · exact u1267
  · exact u1268

theorem m2553_40 : Upper (D 10) (R 10) [6,33,192,96,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1259

theorem m2553_136 : Upper (D 10) (R 10) [6,33,192,96,136] 13 :=
  permutation_upper _ _ _ [6,33,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1265

def r2553 : Route 9 := (fun mask => (mask,id))

def c2553 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2553 : Upper (D 10) (R 10) [6,33,192,96] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96] 13 (by decide) (choices 2) [40,136,160,264,288,384] r2553 c2553
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2553_40
  · exact m2553_136
  · exact u1269
  · exact u1270
  · exact u1271
  · exact u1272

def b2554 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 35 196 200 312 312 376 440 312), lower := (rows 7 35 196 200 16 32 64 128 256), losses := [] }

theorem u2554 : Upper (D 10) (R 10) [6,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2554 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2555_40 : Upper (D 10) (R 10) [6,33,192,272,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1261

theorem m2555_72 : Upper (D 10) (R 10) [6,33,192,272,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1266

theorem m2555_96 : Upper (D 10) (R 10) [6,33,192,272,96] 13 :=
  permutation_upper _ _ _ [6,33,192,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1270

theorem m2555_192 : Upper (D 10) (R 10) [6,33,192,272,192] 13 :=
  permutation_upper _ _ _ [6,33,192,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1273

def r2555 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2555 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2555 : Upper (D 10) (R 10) [6,33,192,272] 13 := by
  apply FastRouting.sound _ _ [6,33,192,272] 13 (by decide) (choices 2) [40,72,96,192,264,288,320] r2555 c2555
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2555_40
  · exact m2555_72
  · exact m2555_96
  · exact m2555_192
  · exact u1275
  · exact u1276
  · exact u1277

theorem m2556_40 : Upper (D 10) (R 10) [6,33,192,288,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1262

theorem m2556_72 : Upper (D 10) (R 10) [6,33,192,288,72] 13 :=
  permutation_upper _ _ _ [6,33,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1267

theorem m2556_96 : Upper (D 10) (R 10) [6,33,192,288,96] 13 :=
  permutation_upper _ _ _ [6,33,192,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1271

theorem m2556_192 : Upper (D 10) (R 10) [6,33,192,288,192] 13 :=
  permutation_upper _ _ _ [6,33,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1274

theorem m2556_264 : Upper (D 10) (R 10) [6,33,192,288,264] 13 :=
  permutation_upper _ _ _ [6,33,192,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1276

def r2556 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2556 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2556 : Upper (D 10) (R 10) [6,33,192,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,288] 13 (by decide) (choices 2) [40,72,96,192,264,288,320] r2556 c2556
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2556_40
  · exact m2556_72
  · exact m2556_96
  · exact m2556_192
  · exact m2556_264
  · exact u1278
  · exact u1279

theorem m2557_40 : Upper (D 10) (R 10) [6,33,192,320,40] 13 :=
  permutation_upper _ _ _ [6,33,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1263

theorem m2557_136 : Upper (D 10) (R 10) [6,33,192,320,136] 13 :=
  permutation_upper _ _ _ [6,33,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1268

theorem m2557_160 : Upper (D 10) (R 10) [6,33,192,320,160] 13 :=
  permutation_upper _ _ _ [6,33,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1272

theorem m2557_264 : Upper (D 10) (R 10) [6,33,192,320,264] 13 :=
  permutation_upper _ _ _ [6,33,192,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1277

theorem m2557_288 : Upper (D 10) (R 10) [6,33,192,320,288] 13 :=
  permutation_upper _ _ _ [6,33,192,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1279

def r2557 : Route 9 := (fun mask => (mask,id))

def c2557 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2557 : Upper (D 10) (R 10) [6,33,192,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,320] 13 (by decide) (choices 2) [40,136,160,264,288,384] r2557 c2557
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2557_40
  · exact m2557_136
  · exact m2557_160
  · exact m2557_264
  · exact m2557_288
  · exact u1280

def b2558 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 11, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 42 52 41 464 480 448 448 448), lower := (rows 7 42 52 41 16 32 64 128 256), losses := [] }

theorem u2558 : Upper (D 10) (R 10) [6,40,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2558 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2559 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2559 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2559 : Upper (D 10) (R 10) [6,40,48,65] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65] 13 (by decide) (choices 2) [96,160,192,384] r2559 c2559
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1282
  · exact u1283
  · exact u1284
  · exact u1285

def b2560 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 52 104 465 481 449 449 449), lower := (rows 7 42 52 104 16 32 64 128 256), losses := [] }

theorem u2560 : Upper (D 10) (R 10) [6,40,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2560 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2561_33 : Upper (D 10) (R 10) [6,40,48,192,33] 13 :=
  permutation_upper _ _ _ [6,40,48,33,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1281

theorem m2561_65 : Upper (D 10) (R 10) [6,40,48,192,65] 13 :=
  permutation_upper _ _ _ [6,40,48,65,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1284

theorem m2561_96 : Upper (D 10) (R 10) [6,40,48,192,96] 13 :=
  permutation_upper _ _ _ [6,40,48,96,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1286

theorem m2561_257 : Upper (D 10) (R 10) [6,40,48,192,257] 13 :=
  permutation_upper _ _ _ [6,40,48,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1285

theorem m2561_288 : Upper (D 10) (R 10) [6,40,48,192,288] 13 :=
  permutation_upper _ _ _ [6,40,48,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1287

def r2561 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2561 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2561 : Upper (D 10) (R 10) [6,40,48,192] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r2561 c2561
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2561_33
  · exact m2561_65
  · exact m2561_96
  · exact u1288
  · exact m2561_257
  · exact m2561_288
  · exact u1289

def b2562 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 69 56 496 480 480 480 480), lower := (rows 7 42 69 56 16 32 64 128 256), losses := [] }

theorem u2562 : Upper (D 10) (R 10) [6,40,65,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2562 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2563 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 69 88 432 416 480 416 416), lower := (rows 7 42 69 88 16 32 64 128 256), losses := [] }

theorem u2563 : Upper (D 10) (R 10) [6,40,65,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2563 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2564 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 69 104 432 432 496 432 432), lower := (rows 7 42 69 104 16 32 64 128 256), losses := [] }

theorem u2564 : Upper (D 10) (R 10) [6,40,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2564 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2565 : Route 9 := (fun mask => (mask,id))

def c2565 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2565 : Upper (D 10) (R 10) [6,40,65,144] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2565 c2565
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1296
  · exact u1297
  · exact u1298
  · exact u1299
  · exact u1300
  · exact u1301

def b2566 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 69 168 496 496 496 496 496), lower := (rows 7 42 69 168 16 32 64 128 256), losses := [] }

theorem u2566 : Upper (D 10) (R 10) [6,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2566 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2567 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 69 200 432 432 496 432 432), lower := (rows 7 42 69 200 16 32 64 128 256), losses := [] }

theorem u2567 : Upper (D 10) (R 10) [6,40,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2567 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2568 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2568 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2568 : Upper (D 10) (R 10) [6,40,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384] 13 (by decide) (choices 2) [96,160,192,384] r2568 c2568
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1308
  · exact u1309
  · exact u1310
  · exact u1311

def b2569 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 84 41 496 480 480 480 480), lower := (rows 7 42 84 41 16 32 64 128 256), losses := [] }

theorem u2569 : Upper (D 10) (R 10) [6,40,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2569 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2570 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 84 73 432 416 480 416 416), lower := (rows 7 42 84 73 16 32 64 128 256), losses := [] }

theorem u2570 : Upper (D 10) (R 10) [6,40,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2570 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2571 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 84 104 433 417 481 417 417), lower := (rows 7 42 84 104 16 32 64 128 256), losses := [] }

theorem u2571 : Upper (D 10) (R 10) [6,40,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2571 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2572 : Route 9 := (fun mask => (mask,id))

def c2572 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2572 : Upper (D 10) (R 10) [6,40,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2572 c2572
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1320
  · exact u1321
  · exact u1322
  · exact u1323
  · exact u1324
  · exact u1325

def b2573 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 84 168 497 481 481 481 481), lower := (rows 7 42 84 168 16 32 64 128 256), losses := [] }

theorem u2573 : Upper (D 10) (R 10) [6,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2573 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2574 : Route 9 := (fun mask => (mask,id))

def c2574 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2574 : Upper (D 10) (R 10) [6,40,80,192] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192] 13 (by decide) (choices 2) [33,129,160,257,288,384] r2574 c2574
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1332
  · exact u1333
  · exact u1334
  · exact u1335
  · exact u1336
  · exact u1337

def r2575 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2575 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2575 : Upper (D 10) (R 10) [6,40,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384] 13 (by decide) (choices 2) [33,65,96,129,160,192,384] r2575 c2575
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1338
  · exact u1339
  · exact u1340
  · exact u1341
  · exact u1342
  · exact u1343
  · exact u1344

theorem m2576_96 : Upper (D 10) (R 10) [6,40,96,17,96] 13 :=
  permutation_upper _ _ _ [6,24,96,33,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1167

theorem m2576_160 : Upper (D 10) (R 10) [6,40,96,17,160] 13 :=
  permutation_upper _ _ _ [6,24,96,33,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1168

theorem m2576_192 : Upper (D 10) (R 10) [6,40,96,17,192] 13 :=
  permutation_upper _ _ _ [6,24,192,33,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1188

theorem m2576_384 : Upper (D 10) (R 10) [6,40,96,17,384] 13 :=
  permutation_upper _ _ _ [6,24,192,33,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1190

def r2576 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2576 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2576 : Upper (D 10) (R 10) [6,40,96,17] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17] 13 (by decide) (choices 2) [96,160,192,384] r2576 c2576
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2576_96
  · exact m2576_160
  · exact m2576_192
  · exact m2576_384

def b2577 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 11, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 42 100 41 464 496 464 464 464), lower := (rows 7 42 100 41 16 32 64 128 256), losses := [] }

theorem u2577 : Upper (D 10) (R 10) [6,40,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2577 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2578 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 100 56 465 481 449 449 449), lower := (rows 7 42 100 56 16 32 64 128 256), losses := [] }

theorem u2578 : Upper (D 10) (R 10) [6,40,96,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2578 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2579 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 100 73 432 432 496 432 432), lower := (rows 7 42 100 73 16 32 64 128 256), losses := [] }

theorem u2579 : Upper (D 10) (R 10) [6,40,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2579 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2579
end Delivery.IrregularNine14.P10
