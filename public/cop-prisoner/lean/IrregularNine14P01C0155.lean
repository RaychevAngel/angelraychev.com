import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0131
import IrregularNine14P01C0132
import IrregularNine14P01C0133
import IrregularNine14P01C0134
import IrregularNine14P01C0135

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m9300_3 : Upper (D 1) (R 1) [268,48,192,3] 13 :=
  permutation_upper _ _ _ [268,48,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7896

theorem m9300_17 : Upper (D 1) (R 1) [268,48,192,17] 13 :=
  permutation_upper _ _ _ [268,48,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7899

theorem m9300_18 : Upper (D 1) (R 1) [268,48,192,18] 13 :=
  permutation_upper _ _ _ [268,48,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7903

theorem m9300_48 : Upper (D 1) (R 1) [268,48,192,48] 13 :=
  permutation_upper _ _ _ [268,48,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7906

theorem m9300_65 : Upper (D 1) (R 1) [268,48,192,65] 13 :=
  permutation_upper _ _ _ [268,48,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7911

theorem m9300_66 : Upper (D 1) (R 1) [268,48,192,66] 13 :=
  permutation_upper _ _ _ [268,48,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7916

theorem m9300_80 : Upper (D 1) (R 1) [268,48,192,80] 13 :=
  permutation_upper _ _ _ [268,48,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7919

def r9300 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9300 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9300 : Upper (D 1) (R 1) [268,48,192] 13 := by
  apply FastRouting.sound _ _ [268,48,192] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] r9300 c9300
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9300_3
  · exact m9300_17
  · exact m9300_18
  · exact m9300_48
  · exact m9300_65
  · exact m9300_66
  · exact m9300_80
  · exact u7920

def b9301 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 275 7 14 248 240 240 240 240 496), lower := (rows 275 7 14 8 16 32 64 128 256), losses := [] }

theorem u9301 : Upper (D 1) (R 1) [274,5,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9301
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9302 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 275 7 22 232 248 232 232 232 488), lower := (rows 275 7 22 8 16 32 64 128 256), losses := [] }

theorem u9302 : Upper (D 1) (R 1) [274,5,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9302
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9303 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 7 28 234 242 226 226 226 482), lower := (rows 275 7 28 8 16 32 64 128 256), losses := [] }

theorem u9303 : Upper (D 1) (R 1) [274,5,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9303
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9304 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 275 7 38 248 248 248 248 248 504), lower := (rows 275 7 38 8 16 32 64 128 256), losses := [] }

theorem u9304 : Upper (D 1) (R 1) [274,5,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9304
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9305 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9305 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9305 : Upper (D 1) (R 1) [274,5,40] 13 := by
  apply FastRouting.sound _ _ [274,5,40] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r9305 c9305
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7921
  · exact u7922
  · exact u7923
  · exact u7924
  · exact u7925
  · exact u7926
  · exact u7927

def b9306 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 7 52 234 250 234 234 234 490), lower := (rows 275 7 52 8 16 32 64 128 256), losses := [] }

theorem u9306 : Upper (D 1) (R 1) [274,5,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9306
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9307 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9307 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9307 : Upper (D 1) (R 1) [274,5,96] 13 := by
  apply FastRouting.sound _ _ [274,5,96] 13 (by decide) (choices 2) [18,34,48,96,130,144,160] r9307 c9307
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7928
  · exact u7929
  · exact u7930
  · exact u7931
  · exact u7932
  · exact u7933
  · exact u7934

def b9308 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 14 7 248 240 240 240 240 496), lower := (rows 275 14 7 8 16 32 64 128 256), losses := [] }

theorem u9308 : Upper (D 1) (R 1) [274,12,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9308
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9309 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 14 21 234 242 226 226 226 482), lower := (rows 275 14 21 8 16 32 64 128 256), losses := [] }

theorem u9309 : Upper (D 1) (R 1) [274,12,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9309
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9310 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 14 22 233 241 225 225 225 481), lower := (rows 275 14 22 8 16 32 64 128 256), losses := [] }

theorem u9310 : Upper (D 1) (R 1) [274,12,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9310
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9311_18 : Upper (D 1) (R 1) [274,12,33,18] 13 :=
  permutation_upper _ _ _ [274,12,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7937

def r9311 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9311 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9311 : Upper (D 1) (R 1) [274,12,33] 13 := by
  apply FastRouting.sound _ _ [274,12,33] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r9311 c9311
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9311_18
  · exact u7939
  · exact u7940
  · exact u7941
  · exact u7942
  · exact u7943
  · exact u7944

def b9312 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 275 14 38 249 241 241 241 241 497), lower := (rows 275 14 38 8 16 32 64 128 256), losses := [] }

theorem u9312 : Upper (D 1) (R 1) [274,12,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9312
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9313 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 14 52 235 243 227 227 227 483), lower := (rows 275 14 52 8 16 32 64 128 256), losses := [] }

theorem u9313 : Upper (D 1) (R 1) [274,12,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9313
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9314_3 : Upper (D 1) (R 1) [274,12,96,3] 13 :=
  permutation_upper _ _ _ [274,12,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7935

theorem m9314_17 : Upper (D 1) (R 1) [274,12,96,17] 13 :=
  permutation_upper _ _ _ [274,12,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7936

theorem m9314_18 : Upper (D 1) (R 1) [274,12,96,18] 13 :=
  permutation_upper _ _ _ [274,12,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7938

theorem m9314_33 : Upper (D 1) (R 1) [274,12,96,33] 13 :=
  permutation_upper _ _ _ [274,12,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7943

theorem m9314_34 : Upper (D 1) (R 1) [274,12,96,34] 13 :=
  permutation_upper _ _ _ [274,12,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7945

theorem m9314_48 : Upper (D 1) (R 1) [274,12,96,48] 13 :=
  permutation_upper _ _ _ [274,12,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7947

theorem m9314_129 : Upper (D 1) (R 1) [274,12,96,129] 13 :=
  permutation_upper _ _ _ [274,12,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7944

theorem m9314_130 : Upper (D 1) (R 1) [274,12,96,130] 13 :=
  permutation_upper _ _ _ [274,12,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7946

theorem m9314_144 : Upper (D 1) (R 1) [274,12,96,144] 13 :=
  permutation_upper _ _ _ [274,12,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7948

def r9314 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9314 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9314 : Upper (D 1) (R 1) [274,12,96] 13 := by
  apply FastRouting.sound _ _ [274,12,96] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r9314 c9314
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9314_3
  · exact m9314_17
  · exact m9314_18
  · exact m9314_33
  · exact m9314_34
  · exact m9314_48
  · exact u7949
  · exact m9314_129
  · exact m9314_130
  · exact m9314_144
  · exact u7950

def b9315 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 14 252 244 244 244 244 500), lower := (rows 275 35 14 8 16 32 64 128 256), losses := [] }

theorem u9315 : Upper (D 1) (R 1) [274,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9315
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9316 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 22 236 252 236 236 236 492), lower := (rows 275 35 22 8 16 32 64 128 256), losses := [] }

theorem u9316 : Upper (D 1) (R 1) [274,33,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9316
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9317_6 : Upper (D 1) (R 1) [274,33,24,6] 13 :=
  permutation_upper _ _ _ [274,33,10,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7951

def r9317 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9317 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9317 : Upper (D 1) (R 1) [274,33,24] 13 := by
  apply FastRouting.sound _ _ [274,33,24] 13 (by decide) (choices 2) [6,34,36,66,68,96,192] r9317 c9317
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9317_6
  · exact u7962
  · exact u7963
  · exact u7964
  · exact u7965
  · exact u7966
  · exact u7967

def b9318 : PairBound 9 := { available := 220, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 35 38 220 220 252 220 220 476), lower := (rows 275 35 38 8 16 32 64 128 256), losses := [] }

theorem u9318 : Upper (D 1) (R 1) [274,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9318
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9319_6 : Upper (D 1) (R 1) [274,33,40,6] 13 :=
  permutation_upper _ _ _ [274,33,10,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7952

theorem m9319_18 : Upper (D 1) (R 1) [274,33,40,18] 13 :=
  permutation_upper _ _ _ [274,33,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7958

theorem m9319_20 : Upper (D 1) (R 1) [274,33,40,20] 13 :=
  permutation_upper _ _ _ [274,33,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7963

def r9319 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9319 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9319 : Upper (D 1) (R 1) [274,33,40] 13 := by
  apply FastRouting.sound _ _ [274,33,40] 13 (by decide) (choices 2) [6,18,20,66,68,80,192] r9319 c9319
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9319_6
  · exact m9319_18
  · exact m9319_20
  · exact u7971
  · exact u7972
  · exact u7973
  · exact u7974

theorem m9320_6 : Upper (D 1) (R 1) [274,33,48,6] 13 :=
  permutation_upper _ _ _ [274,33,10,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7953

def r9320 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9320 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 4 | 36 => 5 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9320 : Upper (D 1) (R 1) [274,33,48] 13 := by
  apply FastRouting.sound _ _ [274,33,48] 13 (by decide) (choices 2) [6,66,68,192] r9320 c9320
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m9320_6
  · exact u7975
  · exact u7976
  · exact u7977

def b9321 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 184, targets := 2 }], pairs := [(3,1)], upper := (rows 275 35 70 252 252 252 252 252 508), lower := (rows 275 35 70 8 16 32 64 128 256), losses := [] }

theorem u9321 : Upper (D 1) (R 1) [274,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9321
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9322_6 : Upper (D 1) (R 1) [274,33,72,6] 13 :=
  permutation_upper _ _ _ [274,33,10,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7954

theorem m9322_18 : Upper (D 1) (R 1) [274,33,72,18] 13 :=
  permutation_upper _ _ _ [274,33,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7959

theorem m9322_20 : Upper (D 1) (R 1) [274,33,72,20] 13 :=
  permutation_upper _ _ _ [274,33,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7965

theorem m9322_34 : Upper (D 1) (R 1) [274,33,72,34] 13 :=
  permutation_upper _ _ _ [274,33,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7968

theorem m9322_36 : Upper (D 1) (R 1) [274,33,72,36] 13 :=
  permutation_upper _ _ _ [274,33,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7972

theorem m9322_48 : Upper (D 1) (R 1) [274,33,72,48] 13 :=
  permutation_upper _ _ _ [274,33,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7976

theorem m9322_66 : Upper (D 1) (R 1) [274,33,72,66] 13 :=
  permutation_upper _ _ _ [274,33,66,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7978

theorem m9322_130 : Upper (D 1) (R 1) [274,33,72,130] 13 :=
  permutation_upper _ _ _ [274,33,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7981

def r9322 : Route 9 := (fun mask => (mask,id))

def c9322 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9322 : Upper (D 1) (R 1) [274,33,72] 13 := by
  apply FastRouting.sound _ _ [274,33,72] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96,130,132,144,160,192] r9322 c9322
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9322_6
  · exact m9322_18
  · exact m9322_20
  · exact m9322_34
  · exact m9322_36
  · exact m9322_48
  · exact m9322_66
  · exact u7985
  · exact u7986
  · exact u7987
  · exact m9322_130
  · exact u7988
  · exact u7989
  · exact u7990
  · exact u7991

theorem m9323_6 : Upper (D 1) (R 1) [274,33,80,6] 13 :=
  permutation_upper _ _ _ [274,33,10,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7955

theorem m9323_34 : Upper (D 1) (R 1) [274,33,80,34] 13 :=
  permutation_upper _ _ _ [274,33,34,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7969

theorem m9323_36 : Upper (D 1) (R 1) [274,33,80,36] 13 :=
  permutation_upper _ _ _ [274,33,40,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7973

theorem m9323_66 : Upper (D 1) (R 1) [274,33,80,66] 13 :=
  permutation_upper _ _ _ [274,33,66,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7979

theorem m9323_68 : Upper (D 1) (R 1) [274,33,80,68] 13 :=
  permutation_upper _ _ _ [274,33,72,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7986

theorem m9323_130 : Upper (D 1) (R 1) [274,33,80,130] 13 :=
  permutation_upper _ _ _ [274,33,66,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7982

theorem m9323_132 : Upper (D 1) (R 1) [274,33,80,132] 13 :=
  permutation_upper _ _ _ [274,33,72,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7989

def r9323 : Route 9 := (fun mask => (mask,id))

def c9323 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9323 : Upper (D 1) (R 1) [274,33,80] 13 := by
  apply FastRouting.sound _ _ [274,33,80] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192] r9323 c9323
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9323_6
  · exact m9323_34
  · exact m9323_36
  · exact m9323_66
  · exact m9323_68
  · exact u7992
  · exact m9323_130
  · exact m9323_132
  · exact u7993
  · exact u7994

theorem m9324_6 : Upper (D 1) (R 1) [274,33,96,6] 13 :=
  permutation_upper _ _ _ [274,33,10,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7956

theorem m9324_18 : Upper (D 1) (R 1) [274,33,96,18] 13 :=
  permutation_upper _ _ _ [274,33,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7960

theorem m9324_20 : Upper (D 1) (R 1) [274,33,96,20] 13 :=
  permutation_upper _ _ _ [274,33,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7966

theorem m9324_66 : Upper (D 1) (R 1) [274,33,96,66] 13 :=
  permutation_upper _ _ _ [274,33,66,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7980

theorem m9324_68 : Upper (D 1) (R 1) [274,33,96,68] 13 :=
  permutation_upper _ _ _ [274,33,72,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7987

theorem m9324_80 : Upper (D 1) (R 1) [274,33,96,80] 13 :=
  permutation_upper _ _ _ [274,33,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7992

theorem m9324_130 : Upper (D 1) (R 1) [274,33,96,130] 13 :=
  permutation_upper _ _ _ [274,33,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7983

theorem m9324_132 : Upper (D 1) (R 1) [274,33,96,132] 13 :=
  permutation_upper _ _ _ [274,33,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7990

theorem m9324_144 : Upper (D 1) (R 1) [274,33,96,144] 13 :=
  permutation_upper _ _ _ [274,33,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7993

def r9324 : Route 9 := (fun mask => (mask,id))

def c9324 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9324 : Upper (D 1) (R 1) [274,33,96] 13 := by
  apply FastRouting.sound _ _ [274,33,96] 13 (by decide) (choices 2) [6,18,20,66,68,80,130,132,144,192] r9324 c9324
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9324_6
  · exact m9324_18
  · exact m9324_20
  · exact m9324_66
  · exact m9324_68
  · exact m9324_80
  · exact m9324_130
  · exact m9324_132
  · exact m9324_144
  · exact u7995

theorem m9325_6 : Upper (D 1) (R 1) [274,33,192,6] 13 :=
  permutation_upper _ _ _ [274,33,10,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7957

theorem m9325_18 : Upper (D 1) (R 1) [274,33,192,18] 13 :=
  permutation_upper _ _ _ [274,33,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7961

theorem m9325_20 : Upper (D 1) (R 1) [274,33,192,20] 13 :=
  permutation_upper _ _ _ [274,33,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7967

theorem m9325_34 : Upper (D 1) (R 1) [274,33,192,34] 13 :=
  permutation_upper _ _ _ [274,33,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7970

theorem m9325_36 : Upper (D 1) (R 1) [274,33,192,36] 13 :=
  permutation_upper _ _ _ [274,33,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7974

theorem m9325_48 : Upper (D 1) (R 1) [274,33,192,48] 13 :=
  permutation_upper _ _ _ [274,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7977

theorem m9325_66 : Upper (D 1) (R 1) [274,33,192,66] 13 :=
  permutation_upper _ _ _ [274,33,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7984

theorem m9325_68 : Upper (D 1) (R 1) [274,33,192,68] 13 :=
  permutation_upper _ _ _ [274,33,72,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7991

theorem m9325_80 : Upper (D 1) (R 1) [274,33,192,80] 13 :=
  permutation_upper _ _ _ [274,33,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7994

theorem m9325_96 : Upper (D 1) (R 1) [274,33,192,96] 13 :=
  permutation_upper _ _ _ [274,33,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7995

def r9325 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9325 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9325 : Upper (D 1) (R 1) [274,33,192] 13 := by
  apply FastRouting.sound _ _ [274,33,192] 13 (by decide) (choices 2) [6,18,20,34,36,48,66,68,80,96,192] r9325 c9325
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9325_6
  · exact m9325_18
  · exact m9325_20
  · exact m9325_34
  · exact m9325_36
  · exact m9325_48
  · exact m9325_66
  · exact m9325_68
  · exact m9325_80
  · exact m9325_96
  · exact u7996

def b9326 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 38 7 248 248 248 248 248 504), lower := (rows 275 38 7 8 16 32 64 128 256), losses := [] }

theorem u9326 : Upper (D 1) (R 1) [274,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9326
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9327 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9327 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9327 : Upper (D 1) (R 1) [274,36,9] 13 := by
  apply FastRouting.sound _ _ [274,36,9] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r9327 c9327
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7997
  · exact u7998
  · exact u7999
  · exact u8000
  · exact u8001
  · exact u8002
  · exact u8003

def b9328 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 275 38 14 249 241 241 241 241 497), lower := (rows 275 38 14 8 16 32 64 128 256), losses := [] }

theorem u9328 : Upper (D 1) (R 1) [274,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9328
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9329 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 38 21 234 250 234 234 234 490), lower := (rows 275 38 21 8 16 32 64 128 256), losses := [] }

theorem u9329 : Upper (D 1) (R 1) [274,36,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9329
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9330 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 22 233 249 233 233 233 489), lower := (rows 275 38 22 8 16 32 64 128 256), losses := [] }

theorem u9330 : Upper (D 1) (R 1) [274,36,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9330
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9331 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 28 235 243 227 227 227 483), lower := (rows 275 38 28 8 16 32 64 128 256), losses := [] }

theorem u9331 : Upper (D 1) (R 1) [274,36,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9331
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9332 : PairBound 9 := { available := 218, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 37 218 218 250 218 218 474), lower := (rows 275 38 37 8 16 32 64 128 256), losses := [] }

theorem u9332 : Upper (D 1) (R 1) [274,36,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9332
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9333 : PairBound 9 := { available := 217, camps := [{ cop := 5, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 38 217 217 249 217 217 473), lower := (rows 275 38 38 8 16 32 64 128 256), losses := [] }

theorem u9333 : Upper (D 1) (R 1) [274,36,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9333
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9334 : PairBound 9 := { available := 211, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 44 219 211 243 211 211 467), lower := (rows 275 38 44 8 16 32 64 128 256), losses := [] }

theorem u9334 : Upper (D 1) (R 1) [274,36,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9334
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9335 : PairBound 9 := { available := 203, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 52 203 219 235 203 203 459), lower := (rows 275 38 52 8 16 32 64 128 256), losses := [] }

theorem u9335 : Upper (D 1) (R 1) [274,36,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9335
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9336 : Route 9 := (fun mask => (mask,id))

def c9336 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9336 : Upper (D 1) (R 1) [274,36,65] 13 := by
  apply FastRouting.sound _ _ [274,36,65] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192] r9336 c9336
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8004
  · exact u8005
  · exact u8006
  · exact u8007
  · exact u8008
  · exact u8009
  · exact u8010
  · exact u8011
  · exact u8012
  · exact u8013

def b9337 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 232, targets := 2 }], pairs := [(3,1)], upper := (rows 275 38 70 249 249 249 249 249 505), lower := (rows 275 38 70 8 16 32 64 128 256), losses := [] }

theorem u9337 : Upper (D 1) (R 1) [274,36,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9337
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9338 : Route 9 := (fun mask => (mask,id))

def c9338 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9338 : Upper (D 1) (R 1) [274,36,72] 13 := by
  apply FastRouting.sound _ _ [274,36,72] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192] r9338 c9338
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8014
  · exact u8015
  · exact u8016
  · exact u8017
  · exact u8018
  · exact u8019
  · exact u8020
  · exact u8021
  · exact u8022
  · exact u8023
  · exact u8024
  · exact u8025
  · exact u8026
  · exact u8027
  · exact u8028

def b9339 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 275 38 84 235 251 235 235 235 491), lower := (rows 275 38 84 8 16 32 64 128 256), losses := [] }

theorem u9339 : Upper (D 1) (R 1) [274,36,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9339
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9340 : PairBound 9 := { available := 219, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 275 38 100 219 219 251 219 219 475), lower := (rows 275 38 100 8 16 32 64 128 256), losses := [] }

theorem u9340 : Upper (D 1) (R 1) [274,36,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9340
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9341 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9341 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9341 : Upper (D 1) (R 1) [274,36,192] 13 := by
  apply FastRouting.sound _ _ [274,36,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r9341 c9341
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8029
  · exact u8030
  · exact u8031
  · exact u8032
  · exact u8033
  · exact u8034
  · exact u8035
  · exact u8036
  · exact u8037
  · exact u8038
  · exact u8039

def b9342 : PairBound 9 := { available := 252, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 7 252 252 252 252 252 508), lower := (rows 275 98 7 8 16 32 64 128 256), losses := [] }

theorem u9342 : Upper (D 1) (R 1) [274,96,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9342
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9343 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9343 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9343 : Upper (D 1) (R 1) [274,96,9] 13 := by
  apply FastRouting.sound _ _ [274,96,9] 13 (by decide) (choices 2) [6,18,20,34,36,48,96,130,132,144,160] r9343 c9343
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8046
  · exact u8047
  · exact u8048
  · exact u8049
  · exact u8050
  · exact u8051
  · exact u8052
  · exact u8053
  · exact u8054
  · exact u8055
  · exact u8056

theorem m9344_5 : Upper (D 1) (R 1) [274,96,10,5] 13 :=
  permutation_upper _ _ _ [274,96,9,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8046

def r9344 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9344 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9344 : Upper (D 1) (R 1) [274,96,10] 13 := by
  apply FastRouting.sound _ _ [274,96,10] 13 (by decide) (choices 2) [5,17,20,33,36,48,96,129,132,144,160] r9344 c9344
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9344_5
  · exact u8057
  · exact u8058
  · exact u8059
  · exact u8060
  · exact u8061
  · exact u8062
  · exact u8063
  · exact u8064
  · exact u8065
  · exact u8066

def b9345 : PairBound 9 := { available := 238, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 275 98 21 238 254 238 238 238 494), lower := (rows 275 98 21 8 16 32 64 128 256), losses := [] }

theorem u9345 : Upper (D 1) (R 1) [274,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9345
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9346 : PairBound 9 := { available := 237, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 22 237 253 237 237 237 493), lower := (rows 275 98 22 8 16 32 64 128 256), losses := [] }

theorem u9346 : Upper (D 1) (R 1) [274,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9346
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9347_3 : Upper (D 1) (R 1) [274,96,24,3] 13 :=
  permutation_upper _ _ _ [274,96,3,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8040

theorem m9347_5 : Upper (D 1) (R 1) [274,96,24,5] 13 :=
  permutation_upper _ _ _ [274,96,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8048

theorem m9347_6 : Upper (D 1) (R 1) [274,96,24,6] 13 :=
  permutation_upper _ _ _ [274,96,10,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8058

def r9347 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9347 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9347 : Upper (D 1) (R 1) [274,96,24] 13 := by
  apply FastRouting.sound _ _ [274,96,24] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160] r9347 c9347
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9347_3
  · exact m9347_5
  · exact m9347_6
  · exact u8076
  · exact u8077
  · exact u8078
  · exact u8079
  · exact u8080
  · exact u8081
  · exact u8082
  · exact u8083

theorem m9348_6 : Upper (D 1) (R 1) [274,96,33,6] 13 :=
  permutation_upper _ _ _ [274,96,10,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8059

theorem m9348_18 : Upper (D 1) (R 1) [274,96,33,18] 13 :=
  permutation_upper _ _ _ [274,96,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8071

theorem m9348_20 : Upper (D 1) (R 1) [274,96,33,20] 13 :=
  permutation_upper _ _ _ [274,96,24,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8076

def r9348 : Route 9 := (fun mask => (mask,id))

def c9348 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9348 : Upper (D 1) (R 1) [274,96,33] 13 := by
  apply FastRouting.sound _ _ [274,96,33] 13 (by decide) (choices 2) [6,18,20,66,68,80,130,132,144,192] r9348 c9348
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9348_6
  · exact m9348_18
  · exact m9348_20
  · exact u8084
  · exact u8085
  · exact u8086
  · exact u8087
  · exact u8088
  · exact u8089
  · exact u8090

def b9349 : PairBound 9 := { available := 221, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 38 221 221 253 221 221 477), lower := (rows 275 98 38 8 16 32 64 128 256), losses := [] }

theorem u9349 : Upper (D 1) (R 1) [274,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9349
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9350_3 : Upper (D 1) (R 1) [274,96,40,3] 13 :=
  permutation_upper _ _ _ [274,96,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8041

theorem m9350_5 : Upper (D 1) (R 1) [274,96,40,5] 13 :=
  permutation_upper _ _ _ [274,96,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8050

theorem m9350_6 : Upper (D 1) (R 1) [274,96,40,6] 13 :=
  permutation_upper _ _ _ [274,96,10,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8060

theorem m9350_17 : Upper (D 1) (R 1) [274,96,40,17] 13 :=
  permutation_upper _ _ _ [274,96,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8067

theorem m9350_18 : Upper (D 1) (R 1) [274,96,40,18] 13 :=
  permutation_upper _ _ _ [274,96,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8072

theorem m9350_20 : Upper (D 1) (R 1) [274,96,40,20] 13 :=
  permutation_upper _ _ _ [274,96,24,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8078

theorem m9350_65 : Upper (D 1) (R 1) [274,96,40,65] 13 :=
  permutation_upper _ _ _ [274,96,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8085

theorem m9350_66 : Upper (D 1) (R 1) [274,96,40,66] 13 :=
  permutation_upper _ _ _ [274,96,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8091

def r9350 : Route 9 := (fun mask => (mask,id))

def c9350 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9350 : Upper (D 1) (R 1) [274,96,40] 13 := by
  apply FastRouting.sound _ _ [274,96,40] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r9350 c9350
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9350_3
  · exact m9350_5
  · exact m9350_6
  · exact m9350_17
  · exact m9350_18
  · exact m9350_20
  · exact m9350_65
  · exact m9350_66
  · exact u8097
  · exact u8098
  · exact u8099
  · exact u8100
  · exact u8101
  · exact u8102
  · exact u8103

theorem m9351_3 : Upper (D 1) (R 1) [274,96,48,3] 13 :=
  permutation_upper _ _ _ [274,96,3,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8042

theorem m9351_5 : Upper (D 1) (R 1) [274,96,48,5] 13 :=
  permutation_upper _ _ _ [274,96,9,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8051

theorem m9351_6 : Upper (D 1) (R 1) [274,96,48,6] 13 :=
  permutation_upper _ _ _ [274,96,10,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8061

theorem m9351_65 : Upper (D 1) (R 1) [274,96,48,65] 13 :=
  permutation_upper _ _ _ [274,96,33,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8086

theorem m9351_66 : Upper (D 1) (R 1) [274,96,48,66] 13 :=
  permutation_upper _ _ _ [274,96,34,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8092

theorem m9351_68 : Upper (D 1) (R 1) [274,96,48,68] 13 :=
  permutation_upper _ _ _ [274,96,40,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8098

def r9351 : Route 9 := (fun mask => (mask,id))

def c9351 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 257 => 8 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 4 | 36 => 5 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9351 : Upper (D 1) (R 1) [274,96,48] 13 := by
  apply FastRouting.sound _ _ [274,96,48] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r9351 c9351
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9351_3
  · exact m9351_5
  · exact m9351_6
  · exact m9351_65
  · exact m9351_66
  · exact m9351_68
  · exact u8104
  · exact u8105
  · exact u8106
  · exact u8107

def b9352 : PairBound 9 := { available := 159, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 100 159 159 191 223 159 415), lower := (rows 275 98 100 8 16 32 64 128 256), losses := [] }

theorem u9352 : Upper (D 1) (R 1) [274,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9352
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9353_6 : Upper (D 1) (R 1) [274,96,129,6] 13 :=
  permutation_upper _ _ _ [274,96,10,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8063

theorem m9353_18 : Upper (D 1) (R 1) [274,96,129,18] 13 :=
  permutation_upper _ _ _ [274,96,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8073

theorem m9353_20 : Upper (D 1) (R 1) [274,96,129,20] 13 :=
  permutation_upper _ _ _ [274,96,24,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8080

theorem m9353_34 : Upper (D 1) (R 1) [274,96,129,34] 13 :=
  permutation_upper _ _ _ [274,96,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8093

theorem m9353_36 : Upper (D 1) (R 1) [274,96,129,36] 13 :=
  permutation_upper _ _ _ [274,96,40,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8099

theorem m9353_48 : Upper (D 1) (R 1) [274,96,129,48] 13 :=
  permutation_upper _ _ _ [274,96,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8104

theorem m9353_96 : Upper (D 1) (R 1) [274,96,129,96] 13 :=
  permutation_upper _ _ _ [274,96,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8108

def r9353 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9353 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9353 : Upper (D 1) (R 1) [274,96,129] 13 := by
  apply FastRouting.sound _ _ [274,96,129] 13 (by decide) (choices 2) [6,18,20,34,36,48,96,130,132,144,160] r9353 c9353
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9353_6
  · exact m9353_18
  · exact m9353_20
  · exact m9353_34
  · exact m9353_36
  · exact m9353_48
  · exact m9353_96
  · exact u8112
  · exact u8113
  · exact u8114
  · exact u8115

theorem m9354_5 : Upper (D 1) (R 1) [274,96,130,5] 13 :=
  permutation_upper _ _ _ [274,96,9,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8053

theorem m9354_17 : Upper (D 1) (R 1) [274,96,130,17] 13 :=
  permutation_upper _ _ _ [274,96,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8068

theorem m9354_20 : Upper (D 1) (R 1) [274,96,130,20] 13 :=
  permutation_upper _ _ _ [274,96,24,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8081

theorem m9354_33 : Upper (D 1) (R 1) [274,96,130,33] 13 :=
  permutation_upper _ _ _ [274,96,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8087

theorem m9354_36 : Upper (D 1) (R 1) [274,96,130,36] 13 :=
  permutation_upper _ _ _ [274,96,40,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8100

theorem m9354_48 : Upper (D 1) (R 1) [274,96,130,48] 13 :=
  permutation_upper _ _ _ [274,96,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8105

theorem m9354_96 : Upper (D 1) (R 1) [274,96,130,96] 13 :=
  permutation_upper _ _ _ [274,96,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8109

theorem m9354_129 : Upper (D 1) (R 1) [274,96,130,129] 13 :=
  permutation_upper _ _ _ [274,96,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8112

def r9354 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9354 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9354 : Upper (D 1) (R 1) [274,96,130] 13 := by
  apply FastRouting.sound _ _ [274,96,130] 13 (by decide) (choices 2) [5,17,20,33,36,48,96,129,132,144,160] r9354 c9354
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9354_5
  · exact m9354_17
  · exact m9354_20
  · exact m9354_33
  · exact m9354_36
  · exact m9354_48
  · exact m9354_96
  · exact m9354_129
  · exact u8116
  · exact u8117
  · exact u8118

theorem m9355_3 : Upper (D 1) (R 1) [274,96,136,3] 13 :=
  permutation_upper _ _ _ [274,96,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8043

theorem m9355_5 : Upper (D 1) (R 1) [274,96,136,5] 13 :=
  permutation_upper _ _ _ [274,96,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8054

theorem m9355_6 : Upper (D 1) (R 1) [274,96,136,6] 13 :=
  permutation_upper _ _ _ [274,96,10,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8064

theorem m9355_17 : Upper (D 1) (R 1) [274,96,136,17] 13 :=
  permutation_upper _ _ _ [274,96,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8069

theorem m9355_18 : Upper (D 1) (R 1) [274,96,136,18] 13 :=
  permutation_upper _ _ _ [274,96,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8074

theorem m9355_20 : Upper (D 1) (R 1) [274,96,136,20] 13 :=
  permutation_upper _ _ _ [274,96,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8082

theorem m9355_33 : Upper (D 1) (R 1) [274,96,136,33] 13 :=
  permutation_upper _ _ _ [274,96,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8088

theorem m9355_34 : Upper (D 1) (R 1) [274,96,136,34] 13 :=
  permutation_upper _ _ _ [274,96,34,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8094

theorem m9355_36 : Upper (D 1) (R 1) [274,96,136,36] 13 :=
  permutation_upper _ _ _ [274,96,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8101

theorem m9355_48 : Upper (D 1) (R 1) [274,96,136,48] 13 :=
  permutation_upper _ _ _ [274,96,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8106

theorem m9355_96 : Upper (D 1) (R 1) [274,96,136,96] 13 :=
  permutation_upper _ _ _ [274,96,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8110

theorem m9355_129 : Upper (D 1) (R 1) [274,96,136,129] 13 :=
  permutation_upper _ _ _ [274,96,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8113

theorem m9355_130 : Upper (D 1) (R 1) [274,96,136,130] 13 :=
  permutation_upper _ _ _ [274,96,130,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8116

def r9355 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9355 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9355 : Upper (D 1) (R 1) [274,96,136] 13 := by
  apply FastRouting.sound _ _ [274,96,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,96,129,130,132,144,160] r9355 c9355
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9355_3
  · exact m9355_5
  · exact m9355_6
  · exact m9355_17
  · exact m9355_18
  · exact m9355_20
  · exact m9355_33
  · exact m9355_34
  · exact m9355_36
  · exact m9355_48
  · exact m9355_96
  · exact m9355_129
  · exact m9355_130
  · exact u8119
  · exact u8120
  · exact u8121

theorem m9356_3 : Upper (D 1) (R 1) [274,96,144,3] 13 :=
  permutation_upper _ _ _ [274,96,3,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8044

theorem m9356_5 : Upper (D 1) (R 1) [274,96,144,5] 13 :=
  permutation_upper _ _ _ [274,96,9,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8055

theorem m9356_6 : Upper (D 1) (R 1) [274,96,144,6] 13 :=
  permutation_upper _ _ _ [274,96,10,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8065

theorem m9356_33 : Upper (D 1) (R 1) [274,96,144,33] 13 :=
  permutation_upper _ _ _ [274,96,33,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8089

theorem m9356_34 : Upper (D 1) (R 1) [274,96,144,34] 13 :=
  permutation_upper _ _ _ [274,96,34,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8095

theorem m9356_36 : Upper (D 1) (R 1) [274,96,144,36] 13 :=
  permutation_upper _ _ _ [274,96,40,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8102

theorem m9356_96 : Upper (D 1) (R 1) [274,96,144,96] 13 :=
  permutation_upper _ _ _ [274,96,96,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8111

theorem m9356_129 : Upper (D 1) (R 1) [274,96,144,129] 13 :=
  permutation_upper _ _ _ [274,96,129,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8114

theorem m9356_130 : Upper (D 1) (R 1) [274,96,144,130] 13 :=
  permutation_upper _ _ _ [274,96,130,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8117

theorem m9356_132 : Upper (D 1) (R 1) [274,96,144,132] 13 :=
  permutation_upper _ _ _ [274,96,136,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8120

def r9356 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9356 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9356 : Upper (D 1) (R 1) [274,96,144] 13 := by
  apply FastRouting.sound _ _ [274,96,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160] r9356 c9356
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9356_3
  · exact m9356_5
  · exact m9356_6
  · exact m9356_33
  · exact m9356_34
  · exact m9356_36
  · exact m9356_96
  · exact m9356_129
  · exact m9356_130
  · exact m9356_132
  · exact u8122

theorem m9357_3 : Upper (D 1) (R 1) [274,96,160,3] 13 :=
  permutation_upper _ _ _ [274,96,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8045

theorem m9357_5 : Upper (D 1) (R 1) [274,96,160,5] 13 :=
  permutation_upper _ _ _ [274,96,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8056

theorem m9357_6 : Upper (D 1) (R 1) [274,96,160,6] 13 :=
  permutation_upper _ _ _ [274,96,10,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8066

theorem m9357_17 : Upper (D 1) (R 1) [274,96,160,17] 13 :=
  permutation_upper _ _ _ [274,96,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8070

theorem m9357_18 : Upper (D 1) (R 1) [274,96,160,18] 13 :=
  permutation_upper _ _ _ [274,96,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8075

theorem m9357_20 : Upper (D 1) (R 1) [274,96,160,20] 13 :=
  permutation_upper _ _ _ [274,96,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8083

theorem m9357_65 : Upper (D 1) (R 1) [274,96,160,65] 13 :=
  permutation_upper _ _ _ [274,96,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8090

theorem m9357_66 : Upper (D 1) (R 1) [274,96,160,66] 13 :=
  permutation_upper _ _ _ [274,96,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8096

theorem m9357_68 : Upper (D 1) (R 1) [274,96,160,68] 13 :=
  permutation_upper _ _ _ [274,96,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8103

theorem m9357_80 : Upper (D 1) (R 1) [274,96,160,80] 13 :=
  permutation_upper _ _ _ [274,96,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8107

theorem m9357_129 : Upper (D 1) (R 1) [274,96,160,129] 13 :=
  permutation_upper _ _ _ [274,96,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8115

theorem m9357_130 : Upper (D 1) (R 1) [274,96,160,130] 13 :=
  permutation_upper _ _ _ [274,96,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8118

theorem m9357_132 : Upper (D 1) (R 1) [274,96,160,132] 13 :=
  permutation_upper _ _ _ [274,96,136,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8121

theorem m9357_144 : Upper (D 1) (R 1) [274,96,160,144] 13 :=
  permutation_upper _ _ _ [274,96,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8122

def r9357 : Route 9 := (fun mask => (mask,id))

def c9357 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 48 => 5 | 272 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9357 : Upper (D 1) (R 1) [274,96,160] 13 := by
  apply FastRouting.sound _ _ [274,96,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192] r9357 c9357
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9357_3
  · exact m9357_5
  · exact m9357_6
  · exact m9357_17
  · exact m9357_18
  · exact m9357_20
  · exact m9357_65
  · exact m9357_66
  · exact m9357_68
  · exact m9357_80
  · exact m9357_129
  · exact m9357_130
  · exact m9357_132
  · exact m9357_144
  · exact u8123

def b9358 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 234, targets := 16 }], pairs := [(1,4)], upper := (rows 277 11 22 234 242 226 226 226 482), lower := (rows 277 11 22 8 16 32 64 128 256), losses := [] }

theorem u9358 : Upper (D 1) (R 1) [276,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9358
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9359 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9359 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9359 : Upper (D 1) (R 1) [276,9,34] 13 := by
  apply FastRouting.sound _ _ [276,9,34] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r9359 c9359
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8124
  · exact u8125
  · exact u8126
  · exact u8127
  · exact u8128
  · exact u8129
  · exact u8130

#print axioms u9359
end Delivery.IrregularNine14.P01
