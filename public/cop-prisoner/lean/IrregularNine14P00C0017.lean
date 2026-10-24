import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0003
import IrregularNine14P00C0004

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1020 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 305 82 164 200 17 34 77 141 269), lower := (rows 305 82 164 200 17 34 64 128 256), losses := [] }

theorem u1020 : Upper (D 0) (R 0) [304,80,160,192,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1020
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1021 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 305 82 164 200 17 36 75 139 267), lower := (rows 305 82 164 200 17 36 64 128 256), losses := [] }

theorem u1021 : Upper (D 0) (R 0) [304,80,160,192,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1021
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1022 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 305 82 164 200 17 40 71 135 263), lower := (rows 305 82 164 200 17 40 64 128 256), losses := [] }

theorem u1022 : Upper (D 0) (R 0) [304,80,160,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1022
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1023 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 15 19 100 392 17 240 240 240 496), lower := (rows 15 19 100 392 17 32 64 128 256), losses := [] }

theorem u1023 : Upper (D 0) (R 0) [14,17,96,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1023
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1024 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 15 19 100 392 48 241 209 209 465), lower := (rows 15 19 100 392 48 32 64 128 256), losses := [] }

theorem u1024 : Upper (D 0) (R 0) [14,17,96,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1024
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1025 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 15 19 100 392 144 113 113 241 369), lower := (rows 15 19 100 392 144 32 64 128 256), losses := [] }

theorem u1025 : Upper (D 0) (R 0) [14,17,96,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1025
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1026 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 15 50 196 265 17 240 240 240 496), lower := (rows 15 50 196 265 17 32 64 128 256), losses := [] }

theorem u1026 : Upper (D 0) (R 0) [14,48,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1026
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1027 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 15 50 196 265 48 241 209 209 465), lower := (rows 15 50 196 265 48 32 64 128 256), losses := [] }

theorem u1027 : Upper (D 0) (R 0) [14,48,192,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1027
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1028_1 : Upper (D 0) (R 0) [14,48,192,257,64,1] 13 :=
  permutation_upper _ _ _ [14,48,192,257,1,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u235

theorem m1028_16 : Upper (D 0) (R 0) [14,48,192,257,64,16] 13 :=
  permutation_upper _ _ _ [14,48,192,257,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u236

def r1028 : Route 9 := (fun mask => (mask,id))

def c1028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1028 : Upper (D 0) (R 0) [14,48,192,257,64] 13 := by
  apply FastRouting.sound _ _ [14,48,192,257,64] 13 (by decide) (choices 1) [1,16,128] r1028 c1028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1028_1
  · exact m1028_16
  · exact u237

def b1029 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 23 11 100 168 17 496 464 464 464), lower := (rows 23 11 100 168 17 32 64 128 256), losses := [] }

theorem u1029 : Upper (D 0) (R 0) [22,9,96,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1029
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1030 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 11 100 168 80 433 465 401 401), lower := (rows 23 11 100 168 80 32 64 128 256), losses := [] }

theorem u1030 : Upper (D 0) (R 0) [22,9,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1030
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1031 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 356, targets := 128 }], pairs := [(2,7)], upper := (rows 23 11 100 168 144 369 337 465 337), lower := (rows 23 11 100 168 144 32 64 128 256), losses := [] }

theorem u1031 : Upper (D 0) (R 0) [22,9,96,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1031
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1032 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 23 11 100 168 272 241 209 209 465), lower := (rows 23 11 100 168 272 32 64 128 256), losses := [] }

theorem u1032 : Upper (D 0) (R 0) [22,9,96,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1032
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1033 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 23 11 100 296 17 240 208 208 464), lower := (rows 23 11 100 296 17 32 64 128 256), losses := [] }

theorem u1033 : Upper (D 0) (R 0) [22,9,96,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1033
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1034 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 11 100 296 80 177 209 145 401), lower := (rows 23 11 100 296 80 32 64 128 256), losses := [] }

theorem u1034 : Upper (D 0) (R 0) [22,9,96,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1034
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1035 : Route 9 := (fun mask => (mask,id))

def c1035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1035 : Upper (D 0) (R 0) [22,9,96,288,128] 13 := by
  apply FastRouting.sound _ _ [22,9,96,288,128] 13 (by decide) (choices 1) [1,16,64,128] r1035 c1035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u238
  · exact u239
  · exact u240
  · exact u241

def b1036 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 23 11 100 392 17 240 240 240 496), lower := (rows 23 11 100 392 17 32 64 128 256), losses := [] }

theorem u1036 : Upper (D 0) (R 0) [22,9,96,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1036
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1037 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 23 11 100 392 48 241 209 209 465), lower := (rows 23 11 100 392 48 32 64 128 256), losses := [] }

theorem u1037 : Upper (D 0) (R 0) [22,9,96,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1037
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1038 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 23 11 100 392 144 113 113 241 369), lower := (rows 23 11 100 392 144 32 64 128 256), losses := [] }

theorem u1038 : Upper (D 0) (R 0) [22,9,96,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1038
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1039 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 23 11 292 104 17 240 208 208 464), lower := (rows 23 11 292 104 17 32 64 128 256), losses := [] }

theorem u1039 : Upper (D 0) (R 0) [22,9,288,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1039
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1040 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 23 11 292 104 80 177 209 145 401), lower := (rows 23 11 292 104 80 32 64 128 256), losses := [] }

theorem u1040 : Upper (D 0) (R 0) [22,9,288,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1040
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1041 : Route 9 := (fun mask => (mask,id))

def c1041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1041 : Upper (D 0) (R 0) [22,9,288,96,128] 13 := by
  apply FastRouting.sound _ _ [22,9,288,96,128] 13 (by decide) (choices 1) [1,16,64,128] r1041 c1041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u242
  · exact u243
  · exact u244
  · exact u245

def b1042 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 23 11 292 200 17 240 240 240 496), lower := (rows 23 11 292 200 17 32 64 128 256), losses := [] }

theorem u1042 : Upper (D 0) (R 0) [22,9,288,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1042
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1043 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 23 11 292 200 48 241 209 209 465), lower := (rows 23 11 292 200 48 32 64 128 256), losses := [] }

theorem u1043 : Upper (D 0) (R 0) [22,9,288,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1043
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1044 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 23 11 292 200 80 177 241 177 433), lower := (rows 23 11 292 200 80 32 64 128 256), losses := [] }

theorem u1044 : Upper (D 0) (R 0) [22,9,288,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1044
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1045 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 76 168 17 496 464 464 464), lower := (rows 23 35 76 168 17 32 64 128 256), losses := [] }

theorem u1045 : Upper (D 0) (R 0) [22,33,72,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1045
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1046 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 76 168 80 433 465 401 401), lower := (rows 23 35 76 168 80 32 64 128 256), losses := [] }

theorem u1046 : Upper (D 0) (R 0) [22,33,72,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1046
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1047 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 23 35 76 168 144 369 337 465 337), lower := (rows 23 35 76 168 144 32 64 128 256), losses := [] }

theorem u1047 : Upper (D 0) (R 0) [22,33,72,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1047
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1048 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 23 35 76 168 272 241 209 209 465), lower := (rows 23 35 76 168 272 32 64 128 256), losses := [] }

theorem u1048 : Upper (D 0) (R 0) [22,33,72,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1048
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1049 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 76 296 17 240 208 208 464), lower := (rows 23 35 76 296 17 32 64 128 256), losses := [] }

theorem u1049 : Upper (D 0) (R 0) [22,33,72,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1049
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1050 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 76 296 80 177 209 145 401), lower := (rows 23 35 76 296 80 32 64 128 256), losses := [] }

theorem u1050 : Upper (D 0) (R 0) [22,33,72,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1050
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1051 : Route 9 := (fun mask => (mask,id))

def c1051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1051 : Upper (D 0) (R 0) [22,33,72,288,128] 13 := by
  apply FastRouting.sound _ _ [22,33,72,288,128] 13 (by decide) (choices 1) [1,16,64,128] r1051 c1051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u246
  · exact u247
  · exact u248
  · exact u249

def b1052 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 76 392 17 240 240 240 496), lower := (rows 23 35 76 392 17 32 64 128 256), losses := [] }

theorem u1052 : Upper (D 0) (R 0) [22,33,72,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1052
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1053 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 76 392 48 241 209 209 465), lower := (rows 23 35 76 392 48 32 64 128 256), losses := [] }

theorem u1053 : Upper (D 0) (R 0) [22,33,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1053
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1054 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 76 392 80 177 241 177 433), lower := (rows 23 35 76 392 80 32 64 128 256), losses := [] }

theorem u1054 : Upper (D 0) (R 0) [22,33,72,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1054
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1055 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 23 35 76 392 144 113 113 241 369), lower := (rows 23 35 76 392 144 32 64 128 256), losses := [] }

theorem u1055 : Upper (D 0) (R 0) [22,33,72,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1055
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1056 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 196 56 17 488 456 456 456), lower := (rows 23 35 196 56 17 32 64 128 256), losses := [] }

theorem u1056 : Upper (D 0) (R 0) [22,33,192,48,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1056
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1057 : PairBound 9 := { available := 449, camps := [], pairs := [], upper := (rows 23 35 196 56 24 481 449 449 449), lower := (rows 23 35 196 56 24 32 64 128 256), losses := [] }

theorem u1057 : Upper (D 0) (R 0) [22,33,192,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1057
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1058 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 196 56 80 425 457 393 393), lower := (rows 23 35 196 56 80 32 64 128 256), losses := [] }

theorem u1058 : Upper (D 0) (R 0) [22,33,192,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1058
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1059 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 23 35 196 56 272 233 201 201 457), lower := (rows 23 35 196 56 272 32 64 128 256), losses := [] }

theorem u1059 : Upper (D 0) (R 0) [22,33,192,48,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1059
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1060 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 196 88 17 424 488 424 424), lower := (rows 23 35 196 88 17 32 64 128 256), losses := [] }

theorem u1060 : Upper (D 0) (R 0) [22,33,192,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1060
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1061 : PairBound 9 := { available := 417, camps := [], pairs := [], upper := (rows 23 35 196 88 24 417 481 417 417), lower := (rows 23 35 196 88 24 32 64 128 256), losses := [] }

theorem u1061 : Upper (D 0) (R 0) [22,33,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1061
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1062 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 196 88 48 425 457 393 393), lower := (rows 23 35 196 88 48 32 64 128 256), losses := [] }

theorem u1062 : Upper (D 0) (R 0) [22,33,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1062
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1063 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 35 196 88 144 297 361 425 297), lower := (rows 23 35 196 88 144 32 64 128 256), losses := [] }

theorem u1063 : Upper (D 0) (R 0) [22,33,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1063
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1064 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 23 35 196 88 272 169 233 169 425), lower := (rows 23 35 196 88 272 32 64 128 256), losses := [] }

theorem u1064 : Upper (D 0) (R 0) [22,33,192,80,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1064
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1065 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 196 104 17 440 472 408 408), lower := (rows 23 35 196 104 17 32 64 128 256), losses := [] }

theorem u1065 : Upper (D 0) (R 0) [22,33,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1065
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1066 : PairBound 9 := { available := 401, camps := [], pairs := [], upper := (rows 23 35 196 104 24 433 465 401 401), lower := (rows 23 35 196 104 24 32 64 128 256), losses := [] }

theorem u1066 : Upper (D 0) (R 0) [22,33,192,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1066
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1067 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 35 196 104 144 313 345 409 281), lower := (rows 23 35 196 104 144 32 64 128 256), losses := [] }

theorem u1067 : Upper (D 0) (R 0) [22,33,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1067
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1068 : PairBound 9 := { available := 153, camps := [], pairs := [], upper := (rows 23 35 196 104 272 185 217 153 409), lower := (rows 23 35 196 104 272 32 64 128 256), losses := [] }

theorem u1068 : Upper (D 0) (R 0) [22,33,192,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1068
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1069 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 196 280 17 232 232 232 488), lower := (rows 23 35 196 280 17 32 64 128 256), losses := [] }

theorem u1069 : Upper (D 0) (R 0) [22,33,192,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1069
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1070 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 23 35 196 280 24 225 225 225 481), lower := (rows 23 35 196 280 24 32 64 128 256), losses := [] }

theorem u1070 : Upper (D 0) (R 0) [22,33,192,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1070
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1071 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 196 280 48 233 201 201 457), lower := (rows 23 35 196 280 48 32 64 128 256), losses := [] }

theorem u1071 : Upper (D 0) (R 0) [22,33,192,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1071
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1072 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 196 280 80 169 233 169 425), lower := (rows 23 35 196 280 80 32 64 128 256), losses := [] }

theorem u1072 : Upper (D 0) (R 0) [22,33,192,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1072
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1073 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 196 296 17 248 216 216 472), lower := (rows 23 35 196 296 17 32 64 128 256), losses := [] }

theorem u1073 : Upper (D 0) (R 0) [22,33,192,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1073
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1074 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 23 35 196 296 24 241 209 209 465), lower := (rows 23 35 196 296 24 32 64 128 256), losses := [] }

theorem u1074 : Upper (D 0) (R 0) [22,33,192,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1074
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1075 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 196 296 80 185 217 153 409), lower := (rows 23 35 196 296 80 32 64 128 256), losses := [] }

theorem u1075 : Upper (D 0) (R 0) [22,33,192,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1075
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1076 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 196 328 17 184 248 184 440), lower := (rows 23 35 196 328 17 32 64 128 256), losses := [] }

theorem u1076 : Upper (D 0) (R 0) [22,33,192,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1076
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1077 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 23 35 196 328 24 177 241 177 433), lower := (rows 23 35 196 328 24 32 64 128 256), losses := [] }

theorem u1077 : Upper (D 0) (R 0) [22,33,192,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1077
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1078 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 196 328 48 185 217 153 409), lower := (rows 23 35 196 328 48 32 64 128 256), losses := [] }

theorem u1078 : Upper (D 0) (R 0) [22,33,192,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1078
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1079 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 35 196 328 144 57 121 185 313), lower := (rows 23 35 196 328 144 32 64 128 256), losses := [] }

theorem u1079 : Upper (D 0) (R 0) [22,33,192,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1079
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1079
end Delivery.IrregularNine14.P00
