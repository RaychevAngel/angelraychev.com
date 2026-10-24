import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0250
import IrregularNine14P08C0251
import IrregularNine14P08C0252
import IrregularNine14P08C0253
import IrregularNine14P08C0254

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21960 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 265 240 240 240 240 496), lower := (rows 193 7 14 265 16 32 64 128 256), losses := [] }

theorem u21960 : Upper (D 8) (R 8) [192,5,10,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r21961 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c21961 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21961 : Upper (D 8) (R 8) [192,5,10,272] 13 := by
  apply FastRouting.sound _ _ [192,5,10,272] 13 (by decide) (choices 2) [33,65,96,192] r21961 c21961
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15110
  · exact u15111
  · exact u15112
  · exact u15113

def r21962 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c21962 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21962 : Upper (D 8) (R 8) [192,5,10,288] 13 := by
  apply FastRouting.sound _ _ [192,5,10,288] 13 (by decide) (choices 2) [33,65,96,192] r21962 c21962
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15114
  · exact u15115
  · exact u15116
  · exact u15117

def b21963 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 328 177 177 241 177 433), lower := (rows 193 7 14 328 16 32 64 128 256), losses := [] }

theorem u21963 : Upper (D 8) (R 8) [192,5,10,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21964 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 21 42 504 488 488 488 488), lower := (rows 193 7 21 42 16 32 64 128 256), losses := [] }

theorem u21964 : Upper (D 8) (R 8) [192,5,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21965 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 21 74 440 424 488 424 424), lower := (rows 193 7 21 74 16 32 64 128 256), losses := [] }

theorem u21965 : Upper (D 8) (R 8) [192,5,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21966 : PairBound 9 := { available := 426, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 21 104 442 426 490 426 426), lower := (rows 193 7 21 104 16 32 64 128 256), losses := [] }

theorem u21966 : Upper (D 8) (R 8) [192,5,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21967 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 21 266 248 232 232 232 488), lower := (rows 193 7 21 266 16 32 64 128 256), losses := [] }

theorem u21967 : Upper (D 8) (R 8) [192,5,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21968 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 21 296 250 234 234 234 490), lower := (rows 193 7 21 296 16 32 64 128 256), losses := [] }

theorem u21968 : Upper (D 8) (R 8) [192,5,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21969 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 21 328 186 170 234 170 426), lower := (rows 193 7 21 328 16 32 64 128 256), losses := [] }

theorem u21969 : Upper (D 8) (R 8) [192,5,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21970 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 464, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 22 41 504 488 488 488 488), lower := (rows 193 7 22 41 16 32 64 128 256), losses := [] }

theorem u21970 : Upper (D 8) (R 8) [192,5,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21971_9 : Upper (D 8) (R 8) [192,5,18,96,9] 13 :=
  permutation_upper _ _ _ [192,5,10,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15082

theorem m21971_33 : Upper (D 8) (R 8) [192,5,18,96,33] 13 :=
  permutation_upper _ _ _ [192,5,10,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15085

theorem m21971_40 : Upper (D 8) (R 8) [192,5,18,96,40] 13 :=
  permutation_upper _ _ _ [192,5,10,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15090

theorem m21971_129 : Upper (D 8) (R 8) [192,5,18,96,129] 13 :=
  permutation_upper _ _ _ [192,5,10,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15095

theorem m21971_136 : Upper (D 8) (R 8) [192,5,18,96,136] 13 :=
  permutation_upper _ _ _ [192,5,10,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15099

theorem m21971_160 : Upper (D 8) (R 8) [192,5,18,96,160] 13 :=
  permutation_upper _ _ _ [192,5,10,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15104

theorem m21971_257 : Upper (D 8) (R 8) [192,5,18,96,257] 13 :=
  permutation_upper _ _ _ [192,5,10,257,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15109

theorem m21971_264 : Upper (D 8) (R 8) [192,5,18,96,264] 13 :=
  permutation_upper _ _ _ [192,5,10,272,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15112

theorem m21971_288 : Upper (D 8) (R 8) [192,5,18,96,288] 13 :=
  permutation_upper _ _ _ [192,5,10,288,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15116

theorem m21971_384 : Upper (D 8) (R 8) [192,5,18,96,384] 13 :=
  permutation_upper _ _ _ [192,5,10,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15119

def r21971 : Route 9 := (fun mask => (mask,id))

def c21971 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21971 : Upper (D 8) (R 8) [192,5,18,96] 13 := by
  apply FastRouting.sound _ _ [192,5,18,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r21971 c21971
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21971_9
  · exact m21971_33
  · exact m21971_40
  · exact m21971_129
  · exact m21971_136
  · exact m21971_160
  · exact m21971_257
  · exact m21971_264
  · exact m21971_288
  · exact m21971_384

def b21972 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 22 265 248 232 232 232 488), lower := (rows 193 7 22 265 16 32 64 128 256), losses := [] }

theorem u21972 : Upper (D 8) (R 8) [192,5,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21973_9 : Upper (D 8) (R 8) [192,5,18,288,9] 13 :=
  permutation_upper _ _ _ [192,5,10,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15083

theorem m21973_33 : Upper (D 8) (R 8) [192,5,18,288,33] 13 :=
  permutation_upper _ _ _ [192,5,10,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15086

theorem m21973_40 : Upper (D 8) (R 8) [192,5,18,288,40] 13 :=
  permutation_upper _ _ _ [192,5,10,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15093

theorem m21973_65 : Upper (D 8) (R 8) [192,5,18,288,65] 13 :=
  permutation_upper _ _ _ [192,5,10,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15096

theorem m21973_72 : Upper (D 8) (R 8) [192,5,18,288,72] 13 :=
  permutation_upper _ _ _ [192,5,10,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15101

theorem m21973_96 : Upper (D 8) (R 8) [192,5,18,288,96] 13 :=
  permutation_upper _ _ _ [192,5,10,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15106

theorem m21973_192 : Upper (D 8) (R 8) [192,5,18,288,192] 13 :=
  permutation_upper _ _ _ [192,5,10,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15108

def r21973 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c21973 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21973 : Upper (D 8) (R 8) [192,5,18,288] 13 := by
  apply FastRouting.sound _ _ [192,5,18,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r21973 c21973
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21973_9
  · exact m21973_33
  · exact m21973_40
  · exact m21973_65
  · exact m21973_72
  · exact m21973_96
  · exact m21973_192

theorem m21974_9 : Upper (D 8) (R 8) [192,5,18,320,9] 13 :=
  permutation_upper _ _ _ [192,5,10,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15084

theorem m21974_33 : Upper (D 8) (R 8) [192,5,18,320,33] 13 :=
  permutation_upper _ _ _ [192,5,10,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15087

theorem m21974_40 : Upper (D 8) (R 8) [192,5,18,320,40] 13 :=
  permutation_upper _ _ _ [192,5,10,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15094

theorem m21974_129 : Upper (D 8) (R 8) [192,5,18,320,129] 13 :=
  permutation_upper _ _ _ [192,5,10,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15097

theorem m21974_136 : Upper (D 8) (R 8) [192,5,18,320,136] 13 :=
  permutation_upper _ _ _ [192,5,10,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15102

theorem m21974_160 : Upper (D 8) (R 8) [192,5,18,320,160] 13 :=
  permutation_upper _ _ _ [192,5,10,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15107

def r21974 : Route 9 := (fun mask => (mask,id))

def c21974 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21974 : Upper (D 8) (R 8) [192,5,18,320] 13 := by
  apply FastRouting.sound _ _ [192,5,18,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r21974 c21974
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21974_9
  · exact m21974_33
  · exact m21974_40
  · exact m21974_129
  · exact m21974_136
  · exact m21974_160

def b21975 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 28 41 498 482 482 482 482), lower := (rows 193 7 28 41 16 32 64 128 256), losses := [] }

theorem u21975 : Upper (D 8) (R 8) [192,5,24,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21976_33 : Upper (D 8) (R 8) [192,5,24,34,33] 13 :=
  permutation_upper _ _ _ [192,5,24,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15120

def r21976 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c21976 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21976 : Upper (D 8) (R 8) [192,5,24,34] 13 := by
  apply FastRouting.sound _ _ [192,5,24,34] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r21976 c21976
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21976_33
  · exact u15126
  · exact u15127
  · exact u15128
  · exact u15129
  · exact u15130
  · exact u15131

def b21977 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 28 73 434 418 482 418 418), lower := (rows 193 7 28 73 16 32 64 128 256), losses := [] }

theorem u21977 : Upper (D 8) (R 8) [192,5,24,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21978 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 28 74 433 417 481 417 417), lower := (rows 193 7 28 74 16 32 64 128 256), losses := [] }

theorem u21978 : Upper (D 8) (R 8) [192,5,24,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21979 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 28 104 435 419 483 419 419), lower := (rows 193 7 28 104 16 32 64 128 256), losses := [] }

theorem u21979 : Upper (D 8) (R 8) [192,5,24,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21980 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 28 200 307 291 355 419 291), lower := (rows 193 7 28 200 16 32 64 128 256), losses := [] }

theorem u21980 : Upper (D 8) (R 8) [192,5,24,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21981 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 28 265 242 226 226 226 482), lower := (rows 193 7 28 265 16 32 64 128 256), losses := [] }

theorem u21981 : Upper (D 8) (R 8) [192,5,24,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21982_33 : Upper (D 8) (R 8) [192,5,24,258,33] 13 :=
  permutation_upper _ _ _ [192,5,24,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15123

theorem m21982_65 : Upper (D 8) (R 8) [192,5,24,258,65] 13 :=
  permutation_upper _ _ _ [192,5,24,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15132

theorem m21982_96 : Upper (D 8) (R 8) [192,5,24,258,96] 13 :=
  permutation_upper _ _ _ [192,5,24,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15140

theorem m21982_192 : Upper (D 8) (R 8) [192,5,24,258,192] 13 :=
  permutation_upper _ _ _ [192,5,24,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15143

def r21982 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c21982 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21982 : Upper (D 8) (R 8) [192,5,24,258] 13 := by
  apply FastRouting.sound _ _ [192,5,24,258] 13 (by decide) (choices 2) [33,65,96,192] r21982 c21982
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m21982_33
  · exact m21982_65
  · exact m21982_96
  · exact m21982_192

theorem m21983_3 : Upper (D 8) (R 8) [192,5,24,288,3] 13 :=
  permutation_upper _ _ _ [192,5,9,18,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15049

theorem m21983_33 : Upper (D 8) (R 8) [192,5,24,288,33] 13 :=
  permutation_upper _ _ _ [192,5,24,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15124

theorem m21983_34 : Upper (D 8) (R 8) [192,5,24,288,34] 13 :=
  permutation_upper _ _ _ [192,5,24,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15130

theorem m21983_65 : Upper (D 8) (R 8) [192,5,24,288,65] 13 :=
  permutation_upper _ _ _ [192,5,24,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15133

theorem m21983_66 : Upper (D 8) (R 8) [192,5,24,288,66] 13 :=
  permutation_upper _ _ _ [192,5,24,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15136

theorem m21983_96 : Upper (D 8) (R 8) [192,5,24,288,96] 13 :=
  permutation_upper _ _ _ [192,5,24,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15141

theorem m21983_192 : Upper (D 8) (R 8) [192,5,24,288,192] 13 :=
  permutation_upper _ _ _ [192,5,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15144

def r21983 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c21983 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21983 : Upper (D 8) (R 8) [192,5,24,288] 13 := by
  apply FastRouting.sound _ _ [192,5,24,288] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r21983 c21983
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21983_3
  · exact m21983_33
  · exact m21983_34
  · exact m21983_65
  · exact m21983_66
  · exact m21983_96
  · exact m21983_192

def b21984 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 28 328 179 163 227 163 419), lower := (rows 193 7 28 328 16 32 64 128 256), losses := [] }

theorem u21984 : Upper (D 8) (R 8) [192,5,24,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21985 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 26 504 488 488 488 488), lower := (rows 193 7 37 26 16 32 64 128 256), losses := [] }

theorem u21985 : Upper (D 8) (R 8) [192,5,33,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21985 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21986 : PairBound 9 := { available := 504, camps := [{ cop := 2, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 37 42 504 504 504 504 504), lower := (rows 193 7 37 42 16 32 64 128 256), losses := [] }

theorem u21986 : Upper (D 8) (R 8) [192,5,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21987 : PairBound 9 := { available := 440, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 74 440 440 504 440 440), lower := (rows 193 7 37 74 16 32 64 128 256), losses := [] }

theorem u21987 : Upper (D 8) (R 8) [192,5,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21987 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21988 : PairBound 9 := { available := 442, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 104 442 442 506 442 442), lower := (rows 193 7 37 104 16 32 64 128 256), losses := [] }

theorem u21988 : Upper (D 8) (R 8) [192,5,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21988 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21989 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 266 248 248 248 248 504), lower := (rows 193 7 37 266 16 32 64 128 256), losses := [] }

theorem u21989 : Upper (D 8) (R 8) [192,5,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21990 : PairBound 9 := { available := 250, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 296 250 250 250 250 506), lower := (rows 193 7 37 296 16 32 64 128 256), losses := [] }

theorem u21990 : Upper (D 8) (R 8) [192,5,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21991 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 37 328 186 186 250 186 442), lower := (rows 193 7 37 328 16 32 64 128 256), losses := [] }

theorem u21991 : Upper (D 8) (R 8) [192,5,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21992 : PairBound 9 := { available := 488, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 38 25 504 488 488 488 488), lower := (rows 193 7 38 25 16 32 64 128 256), losses := [] }

theorem u21992 : Upper (D 8) (R 8) [192,5,34,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21993 : PairBound 9 := { available := 504, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 41 504 504 504 504 504), lower := (rows 193 7 38 41 16 32 64 128 256), losses := [] }

theorem u21993 : Upper (D 8) (R 8) [192,5,34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21994_9 : Upper (D 8) (R 8) [192,5,34,48,9] 13 :=
  permutation_upper _ _ _ [192,5,34,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15173

theorem m21994_33 : Upper (D 8) (R 8) [192,5,34,48,33] 13 :=
  permutation_upper _ _ _ [192,5,34,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15179

def r21994 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c21994 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u21994 : Upper (D 8) (R 8) [192,5,34,48] 13 := by
  apply FastRouting.sound _ _ [192,5,34,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,192,257,264,288,320] r21994 c21994
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21994_9
  · exact m21994_33
  · exact u15185
  · exact u15186
  · exact u15187
  · exact u15188
  · exact u15189
  · exact u15190
  · exact u15191
  · exact u15192
  · exact u15193

def b21995 : PairBound 9 := { available := 440, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 38 73 440 440 504 440 440), lower := (rows 193 7 38 73 16 32 64 128 256), losses := [] }

theorem u21995 : Upper (D 8) (R 8) [192,5,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21996_9 : Upper (D 8) (R 8) [192,5,34,80,9] 13 :=
  permutation_upper _ _ _ [192,5,34,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15174

theorem m21996_33 : Upper (D 8) (R 8) [192,5,34,80,33] 13 :=
  permutation_upper _ _ _ [192,5,34,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15180

theorem m21996_40 : Upper (D 8) (R 8) [192,5,34,80,40] 13 :=
  permutation_upper _ _ _ [192,5,34,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15187

theorem m21996_129 : Upper (D 8) (R 8) [192,5,34,80,129] 13 :=
  permutation_upper _ _ _ [192,5,34,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15194

def r21996 : Route 9 := (fun mask => (mask,id))

def c21996 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21996 : Upper (D 8) (R 8) [192,5,34,80] 13 := by
  apply FastRouting.sound _ _ [192,5,34,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r21996 c21996
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21996_9
  · exact m21996_33
  · exact m21996_40
  · exact m21996_129
  · exact u15199
  · exact u15200
  · exact u15201
  · exact u15202
  · exact u15203
  · exact u15204

theorem m21997_9 : Upper (D 8) (R 8) [192,5,34,96,9] 13 :=
  permutation_upper _ _ _ [192,5,34,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15175

theorem m21997_33 : Upper (D 8) (R 8) [192,5,34,96,33] 13 :=
  permutation_upper _ _ _ [192,5,34,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15181

theorem m21997_40 : Upper (D 8) (R 8) [192,5,34,96,40] 13 :=
  permutation_upper _ _ _ [192,5,34,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15188

theorem m21997_129 : Upper (D 8) (R 8) [192,5,34,96,129] 13 :=
  permutation_upper _ _ _ [192,5,34,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15195

theorem m21997_136 : Upper (D 8) (R 8) [192,5,34,96,136] 13 :=
  permutation_upper _ _ _ [192,5,34,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15200

def r21997 : Route 9 := (fun mask => (mask,id))

def c21997 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21997 : Upper (D 8) (R 8) [192,5,34,96] 13 := by
  apply FastRouting.sound _ _ [192,5,34,96] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r21997 c21997
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21997_9
  · exact m21997_33
  · exact m21997_40
  · exact m21997_129
  · exact m21997_136
  · exact u15205
  · exact u15206
  · exact u15207
  · exact u15208
  · exact u15209

def b21998 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 38 200 313 313 377 441 313), lower := (rows 193 7 38 200 16 32 64 128 256), losses := [] }

theorem u21998 : Upper (D 8) (R 8) [192,5,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21999 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 38 265 248 248 248 248 504), lower := (rows 193 7 38 265 16 32 64 128 256), losses := [] }

theorem u21999 : Upper (D 8) (R 8) [192,5,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21999 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22000_9 : Upper (D 8) (R 8) [192,5,34,272,9] 13 :=
  permutation_upper _ _ _ [192,5,34,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15176

theorem m22000_33 : Upper (D 8) (R 8) [192,5,34,272,33] 13 :=
  permutation_upper _ _ _ [192,5,34,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15182

theorem m22000_40 : Upper (D 8) (R 8) [192,5,34,272,40] 13 :=
  permutation_upper _ _ _ [192,5,34,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15191

theorem m22000_65 : Upper (D 8) (R 8) [192,5,34,272,65] 13 :=
  permutation_upper _ _ _ [192,5,34,65,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15196

theorem m22000_72 : Upper (D 8) (R 8) [192,5,34,272,72] 13 :=
  permutation_upper _ _ _ [192,5,34,80,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15202

theorem m22000_96 : Upper (D 8) (R 8) [192,5,34,272,96] 13 :=
  permutation_upper _ _ _ [192,5,34,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15207

theorem m22000_192 : Upper (D 8) (R 8) [192,5,34,272,192] 13 :=
  permutation_upper _ _ _ [192,5,34,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15210

def r22000 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22000 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22000 : Upper (D 8) (R 8) [192,5,34,272] 13 := by
  apply FastRouting.sound _ _ [192,5,34,272] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22000 c22000
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22000_9
  · exact m22000_33
  · exact m22000_40
  · exact m22000_65
  · exact m22000_72
  · exact m22000_96
  · exact m22000_192

theorem m22001_9 : Upper (D 8) (R 8) [192,5,34,288,9] 13 :=
  permutation_upper _ _ _ [192,5,34,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15177

theorem m22001_33 : Upper (D 8) (R 8) [192,5,34,288,33] 13 :=
  permutation_upper _ _ _ [192,5,34,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15183

theorem m22001_40 : Upper (D 8) (R 8) [192,5,34,288,40] 13 :=
  permutation_upper _ _ _ [192,5,34,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15192

theorem m22001_65 : Upper (D 8) (R 8) [192,5,34,288,65] 13 :=
  permutation_upper _ _ _ [192,5,34,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15197

theorem m22001_72 : Upper (D 8) (R 8) [192,5,34,288,72] 13 :=
  permutation_upper _ _ _ [192,5,34,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15203

theorem m22001_96 : Upper (D 8) (R 8) [192,5,34,288,96] 13 :=
  permutation_upper _ _ _ [192,5,34,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15208

theorem m22001_192 : Upper (D 8) (R 8) [192,5,34,288,192] 13 :=
  permutation_upper _ _ _ [192,5,34,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15211

def r22001 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22001 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22001 : Upper (D 8) (R 8) [192,5,34,288] 13 := by
  apply FastRouting.sound _ _ [192,5,34,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22001 c22001
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22001_9
  · exact m22001_33
  · exact m22001_40
  · exact m22001_65
  · exact m22001_72
  · exact m22001_96
  · exact m22001_192

theorem m22002_9 : Upper (D 8) (R 8) [192,5,34,320,9] 13 :=
  permutation_upper _ _ _ [192,5,34,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15178

theorem m22002_33 : Upper (D 8) (R 8) [192,5,34,320,33] 13 :=
  permutation_upper _ _ _ [192,5,34,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15184

theorem m22002_40 : Upper (D 8) (R 8) [192,5,34,320,40] 13 :=
  permutation_upper _ _ _ [192,5,34,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15193

theorem m22002_129 : Upper (D 8) (R 8) [192,5,34,320,129] 13 :=
  permutation_upper _ _ _ [192,5,34,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15198

theorem m22002_136 : Upper (D 8) (R 8) [192,5,34,320,136] 13 :=
  permutation_upper _ _ _ [192,5,34,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15204

theorem m22002_160 : Upper (D 8) (R 8) [192,5,34,320,160] 13 :=
  permutation_upper _ _ _ [192,5,34,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15209

def r22002 : Route 9 := (fun mask => (mask,id))

def c22002 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22002 : Upper (D 8) (R 8) [192,5,34,320] 13 := by
  apply FastRouting.sound _ _ [192,5,34,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22002 c22002
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22002_9
  · exact m22002_33
  · exact m22002_40
  · exact m22002_129
  · exact m22002_136
  · exact m22002_160

def b22003 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 25 498 482 482 482 482), lower := (rows 193 7 44 25 16 32 64 128 256), losses := [] }

theorem u22003 : Upper (D 8) (R 8) [192,5,40,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22003 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22004 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22004 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u22004 : Upper (D 8) (R 8) [192,5,40,18] 13 := by
  apply FastRouting.sound _ _ [192,5,40,18] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r22004 c22004
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u15218
  · exact u15219
  · exact u15220
  · exact u15221
  · exact u15222
  · exact u15223
  · exact u15224

def b22005 : PairBound 9 := { available := 498, camps := [{ cop := 3, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 41 498 498 498 498 498), lower := (rows 193 7 44 41 16 32 64 128 256), losses := [] }

theorem u22005 : Upper (D 8) (R 8) [192,5,40,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22005 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22006 : PairBound 9 := { available := 497, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 42 497 497 497 497 497), lower := (rows 193 7 44 42 16 32 64 128 256), losses := [] }

theorem u22006 : Upper (D 8) (R 8) [192,5,40,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22006 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22007 : PairBound 9 := { available := 483, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 56 499 483 483 483 483), lower := (rows 193 7 44 56 16 32 64 128 256), losses := [] }

theorem u22007 : Upper (D 8) (R 8) [192,5,40,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22007 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22008 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 44 73 434 434 498 434 434), lower := (rows 193 7 44 73 16 32 64 128 256), losses := [] }

theorem u22008 : Upper (D 8) (R 8) [192,5,40,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22008 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22009 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 74 433 433 497 433 433), lower := (rows 193 7 44 74 16 32 64 128 256), losses := [] }

theorem u22009 : Upper (D 8) (R 8) [192,5,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22009 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22010 : PairBound 9 := { available := 419, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 88 435 419 483 419 419), lower := (rows 193 7 44 88 16 32 64 128 256), losses := [] }

theorem u22010 : Upper (D 8) (R 8) [192,5,40,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22010 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22011 : PairBound 9 := { available := 435, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 104 435 435 499 435 435), lower := (rows 193 7 44 104 16 32 64 128 256), losses := [] }

theorem u22011 : Upper (D 8) (R 8) [192,5,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22011 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22012 : PairBound 9 := { available := 307, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 44 200 307 307 371 435 307), lower := (rows 193 7 44 200 16 32 64 128 256), losses := [] }

theorem u22012 : Upper (D 8) (R 8) [192,5,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22012 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22013 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 44 265 242 242 242 242 498), lower := (rows 193 7 44 265 16 32 64 128 256), losses := [] }

theorem u22013 : Upper (D 8) (R 8) [192,5,40,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22013 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22014 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22014 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22014 : Upper (D 8) (R 8) [192,5,40,258] 13 := by
  apply FastRouting.sound _ _ [192,5,40,258] 13 (by decide) (choices 2) [33,65,96,192] r22014 c22014
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15279
  · exact u15280
  · exact u15281
  · exact u15282

theorem m22015_3 : Upper (D 8) (R 8) [192,5,40,272,3] 13 :=
  permutation_upper _ _ _ [192,5,9,48,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15055

def r22015 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22015 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22015 : Upper (D 8) (R 8) [192,5,40,272] 13 := by
  apply FastRouting.sound _ _ [192,5,40,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r22015 c22015
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22015_3
  · exact u15283
  · exact u15284
  · exact u15285
  · exact u15286
  · exact u15287
  · exact u15288

def b22016 : PairBound 9 := { available := 243, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 193 7 44 296 243 243 243 243 499), lower := (rows 193 7 44 296 16 32 64 128 256), losses := [] }

theorem u22016 : Upper (D 8) (R 8) [192,5,40,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22016 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22017 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 44 328 179 179 243 179 435), lower := (rows 193 7 44 328 16 32 64 128 256), losses := [] }

theorem u22017 : Upper (D 8) (R 8) [192,5,40,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22017 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22018_10 : Upper (D 8) (R 8) [192,5,48,33,10] 13 :=
  permutation_upper _ _ _ [192,5,40,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15218

theorem m22018_34 : Upper (D 8) (R 8) [192,5,48,33,34] 13 :=
  permutation_upper _ _ _ [192,5,40,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15231

theorem m22018_40 : Upper (D 8) (R 8) [192,5,48,33,40] 13 :=
  permutation_upper _ _ _ [192,5,40,48,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15236

theorem m22018_66 : Upper (D 8) (R 8) [192,5,48,33,66] 13 :=
  permutation_upper _ _ _ [192,5,40,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15250

theorem m22018_72 : Upper (D 8) (R 8) [192,5,48,33,72] 13 :=
  permutation_upper _ _ _ [192,5,40,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15255

theorem m22018_96 : Upper (D 8) (R 8) [192,5,48,33,96] 13 :=
  permutation_upper _ _ _ [192,5,40,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15263

theorem m22018_192 : Upper (D 8) (R 8) [192,5,48,33,192] 13 :=
  permutation_upper _ _ _ [192,5,40,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15271

theorem m22018_258 : Upper (D 8) (R 8) [192,5,48,33,258] 13 :=
  permutation_upper _ _ _ [192,5,40,258,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15279

theorem m22018_264 : Upper (D 8) (R 8) [192,5,48,33,264] 13 :=
  permutation_upper _ _ _ [192,5,40,272,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15283

theorem m22018_288 : Upper (D 8) (R 8) [192,5,48,33,288] 13 :=
  permutation_upper _ _ _ [192,5,40,288,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15289

theorem m22018_320 : Upper (D 8) (R 8) [192,5,48,33,320] 13 :=
  permutation_upper _ _ _ [192,5,40,320,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15293

def r22018 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22018 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u22018 : Upper (D 8) (R 8) [192,5,48,33] 13 := by
  apply FastRouting.sound _ _ [192,5,48,33] 13 (by decide) (choices 2) [10,34,40,66,72,96,192,258,264,288,320] r22018 c22018
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22018_10
  · exact m22018_34
  · exact m22018_40
  · exact m22018_66
  · exact m22018_72
  · exact m22018_96
  · exact m22018_192
  · exact m22018_258
  · exact m22018_264
  · exact m22018_288
  · exact m22018_320

theorem m22019_9 : Upper (D 8) (R 8) [192,5,48,34,9] 13 :=
  permutation_upper _ _ _ [192,5,40,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15212

theorem m22019_33 : Upper (D 8) (R 8) [192,5,48,34,33] 13 :=
  permutation_upper _ _ _ [192,5,40,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15225

theorem m22019_40 : Upper (D 8) (R 8) [192,5,48,34,40] 13 :=
  permutation_upper _ _ _ [192,5,40,48,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15237

theorem m22019_65 : Upper (D 8) (R 8) [192,5,48,34,65] 13 :=
  permutation_upper _ _ _ [192,5,40,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15244

theorem m22019_72 : Upper (D 8) (R 8) [192,5,48,34,72] 13 :=
  permutation_upper _ _ _ [192,5,40,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15256

theorem m22019_96 : Upper (D 8) (R 8) [192,5,48,34,96] 13 :=
  permutation_upper _ _ _ [192,5,40,96,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15264

theorem m22019_192 : Upper (D 8) (R 8) [192,5,48,34,192] 13 :=
  permutation_upper _ _ _ [192,5,40,192,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15272

theorem m22019_257 : Upper (D 8) (R 8) [192,5,48,34,257] 13 :=
  permutation_upper _ _ _ [192,5,40,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15276

theorem m22019_264 : Upper (D 8) (R 8) [192,5,48,34,264] 13 :=
  permutation_upper _ _ _ [192,5,40,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15284

theorem m22019_288 : Upper (D 8) (R 8) [192,5,48,34,288] 13 :=
  permutation_upper _ _ _ [192,5,40,288,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15290

theorem m22019_320 : Upper (D 8) (R 8) [192,5,48,34,320] 13 :=
  permutation_upper _ _ _ [192,5,40,320,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15294

def r22019 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22019 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u22019 : Upper (D 8) (R 8) [192,5,48,34] 13 := by
  apply FastRouting.sound _ _ [192,5,48,34] 13 (by decide) (choices 2) [9,33,40,65,72,96,192,257,264,288,320] r22019 c22019
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22019_9
  · exact m22019_33
  · exact m22019_40
  · exact m22019_65
  · exact m22019_72
  · exact m22019_96
  · exact m22019_192
  · exact m22019_257
  · exact m22019_264
  · exact m22019_288
  · exact m22019_320

#print axioms u22019
end Delivery.IrregularNine14.P08
