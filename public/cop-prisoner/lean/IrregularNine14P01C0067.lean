import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0017
import IrregularNine14P01C0018

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4020 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 292 137 80 170 202 138 394), lower := (rows 113 22 292 137 80 32 64 128 256), losses := [] }

theorem u4020 : Upper (D 1) (R 1) [112,20,288,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4020
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4021 : Route 9 := (fun mask => (mask,id))

def c4021 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4021 : Upper (D 1) (R 1) [112,20,288,129,128] 13 := by
  apply FastRouting.sound _ _ [112,20,288,129,128] 13 (by decide) (choices 1) [2,8,64] r4021 c4021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1075
  · exact u1076
  · exact u1077

def b4022 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 22 292 138 17 234 202 202 458), lower := (rows 113 22 292 138 17 32 64 128 256), losses := [] }

theorem u4022 : Upper (D 1) (R 1) [112,20,288,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4022
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4023 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 292 138 18 233 201 201 457), lower := (rows 113 22 292 138 18 32 64 128 256), losses := [] }

theorem u4023 : Upper (D 1) (R 1) [112,20,288,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4023
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4024 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 292 138 24 227 195 195 451), lower := (rows 113 22 292 138 24 32 64 128 256), losses := [] }

theorem u4024 : Upper (D 1) (R 1) [112,20,288,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4024
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4025 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 292 138 80 171 203 139 395), lower := (rows 113 22 292 138 80 32 64 128 256), losses := [] }

theorem u4025 : Upper (D 1) (R 1) [112,20,288,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4025
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4026 : Route 9 := (fun mask => (mask,id))

def c4026 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4026 : Upper (D 1) (R 1) [112,20,288,130,128] 13 := by
  apply FastRouting.sound _ _ [112,20,288,130,128] 13 (by decide) (choices 1) [1,2,8,64] r4026 c4026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1078
  · exact u1079
  · exact u1080
  · exact u1081

def b4027 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 113 22 292 200 17 170 202 138 394), lower := (rows 113 22 292 200 17 32 64 128 256), losses := [] }

theorem u4027 : Upper (D 1) (R 1) [112,20,288,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4027
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4028 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 292 200 18 171 203 139 395), lower := (rows 113 22 292 200 18 32 64 128 256), losses := [] }

theorem u4028 : Upper (D 1) (R 1) [112,20,288,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4028
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4029 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 22 292 200 24 163 195 131 387), lower := (rows 113 22 292 200 24 32 64 128 256), losses := [] }

theorem u4029 : Upper (D 1) (R 1) [112,20,288,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4029
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4030 : Route 9 := (fun mask => (mask,id))

def c4030 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4030 : Upper (D 1) (R 1) [112,20,288,192,128] 13 := by
  apply FastRouting.sound _ _ [112,20,288,192,128] 13 (by decide) (choices 1) [1,2,8] r4030 c4030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1082
  · exact u1083
  · exact u1084

def b4031 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 22 388 42 17 234 202 202 458), lower := (rows 113 22 388 42 17 32 64 128 256), losses := [] }

theorem u4031 : Upper (D 1) (R 1) [112,20,384,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4031
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4032 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 388 42 18 233 201 201 457), lower := (rows 113 22 388 42 18 32 64 128 256), losses := [] }

theorem u4032 : Upper (D 1) (R 1) [112,20,384,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4032
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4033 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 22 388 42 24 227 195 195 451), lower := (rows 113 22 388 42 24 32 64 128 256), losses := [] }

theorem u4033 : Upper (D 1) (R 1) [112,20,384,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4033
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4034 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 388 42 80 171 203 139 395), lower := (rows 113 22 388 42 80 32 64 128 256), losses := [] }

theorem u4034 : Upper (D 1) (R 1) [112,20,384,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4034
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4035 : PairBound 9 := { available := 75, camps := [{ cop := 1, region := 105, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 388 42 144 107 75 203 331), lower := (rows 113 22 388 42 144 32 64 128 256), losses := [] }

theorem u4035 : Upper (D 1) (R 1) [112,20,384,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4035
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4036 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 388 137 18 106 106 234 362), lower := (rows 113 22 388 137 18 32 64 128 256), losses := [] }

theorem u4036 : Upper (D 1) (R 1) [112,20,384,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4036
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4037 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 22 388 137 24 98 98 226 354), lower := (rows 113 22 388 137 24 32 64 128 256), losses := [] }

theorem u4037 : Upper (D 1) (R 1) [112,20,384,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4037
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4038 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 388 137 48 106 74 202 330), lower := (rows 113 22 388 137 48 32 64 128 256), losses := [] }

theorem u4038 : Upper (D 1) (R 1) [112,20,384,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4038
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4039 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 22 388 168 17 106 74 202 330), lower := (rows 113 22 388 168 17 32 64 128 256), losses := [] }

theorem u4039 : Upper (D 1) (R 1) [112,20,384,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4039
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4040 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 388 168 18 107 75 203 331), lower := (rows 113 22 388 168 18 32 64 128 256), losses := [] }

theorem u4040 : Upper (D 1) (R 1) [112,20,384,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4040
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4041 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 22 388 168 24 99 67 195 323), lower := (rows 113 22 388 168 24 32 64 128 256), losses := [] }

theorem u4041 : Upper (D 1) (R 1) [112,20,384,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4041
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4042 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 388 168 80 43 75 139 267), lower := (rows 113 22 388 168 80 32 64 128 256), losses := [] }

theorem u4042 : Upper (D 1) (R 1) [112,20,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4042
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4043 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 131 14 268 18 240 240 240 496), lower := (rows 113 131 14 268 18 32 64 128 256), losses := [] }

theorem u4043 : Upper (D 1) (R 1) [112,129,10,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4043
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4044 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 130, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 14 268 48 242 210 210 466), lower := (rows 113 131 14 268 48 32 64 128 256), losses := [] }

theorem u4044 : Upper (D 1) (R 1) [112,129,10,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4044
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4045_2 : Upper (D 1) (R 1) [112,129,10,260,128,2] 13 :=
  permutation_upper _ _ _ [112,129,10,260,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1085

theorem m4045_16 : Upper (D 1) (R 1) [112,129,10,260,128,16] 13 :=
  permutation_upper _ _ _ [112,129,10,260,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1086

theorem m4045_64 : Upper (D 1) (R 1) [112,129,10,260,128,64] 13 :=
  permutation_upper _ _ _ [112,129,10,260,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1087

def r4045 : Route 9 := (fun mask => (mask,id))

def c4045 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4045 : Upper (D 1) (R 1) [112,129,10,260,128] 13 := by
  apply FastRouting.sound _ _ [112,129,10,260,128] 13 (by decide) (choices 1) [2,16,64] r4045 c4045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4045_2
  · exact m4045_16
  · exact m4045_64

def r4046 : Route 9 := (fun mask => (mask,id))

def c4046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4046 : Upper (D 1) (R 1) [112,129,10,272,2] 13 := by
  apply FastRouting.sound _ _ [112,129,10,272,2] 13 (by decide) (choices 1) [4,64,128] r4046 c4046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1088
  · exact u1089
  · exact u1090

def b4047 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 131 14 280 20 226 226 226 482), lower := (rows 113 131 14 280 20 32 64 128 256), losses := [] }

theorem u4047 : Upper (D 1) (R 1) [112,129,10,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4047
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4048 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 14 280 48 230 198 198 454), lower := (rows 113 131 14 280 48 32 64 128 256), losses := [] }

theorem u4048 : Upper (D 1) (R 1) [112,129,10,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4048
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4049 : Route 9 := (fun mask => (mask,id))

def c4049 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4049 : Upper (D 1) (R 1) [112,129,10,272,128] 13 := by
  apply FastRouting.sound _ _ [112,129,10,272,128] 13 (by decide) (choices 1) [2,4,64] r4049 c4049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1091
  · exact u1092
  · exact u1093

def r4050 : Route 9 := (fun mask => (mask,id))

def c4050 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u4050 : Upper (D 1) (R 1) [112,129,24,160,2] 13 := by
  apply FastRouting.sound _ _ [112,129,24,160,2] 13 (by decide) (choices 1) [2,4,64,256] r4050 c4050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1094
  · exact u1095
  · exact u1096
  · exact u1097

def b4051 : PairBound 9 := { available := 322, camps := [], pairs := [], upper := (rows 113 131 28 168 20 354 322 450 322), lower := (rows 113 131 28 168 20 32 64 128 256), losses := [] }

theorem u4051 : Upper (D 1) (R 1) [112,129,24,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4051
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4052 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 28 168 80 294 326 390 262), lower := (rows 113 131 28 168 80 32 64 128 256), losses := [] }

theorem u4052 : Upper (D 1) (R 1) [112,129,24,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4052
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4053 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 131 28 168 272 102 70 198 326), lower := (rows 113 131 28 168 272 32 64 128 256), losses := [] }

theorem u4053 : Upper (D 1) (R 1) [112,129,24,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4053
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4054 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 28 266 18 228 228 228 484), lower := (rows 113 131 28 266 18 32 64 128 256), losses := [] }

theorem u4054 : Upper (D 1) (R 1) [112,129,24,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4054
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4055 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 131 28 266 20 226 226 226 482), lower := (rows 113 131 28 266 20 32 64 128 256), losses := [] }

theorem u4055 : Upper (D 1) (R 1) [112,129,24,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4055
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4056 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 28 266 48 230 198 198 454), lower := (rows 113 131 28 266 48 32 64 128 256), losses := [] }

theorem u4056 : Upper (D 1) (R 1) [112,129,24,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4056
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4057 : PairBound 9 := { available := 102, camps := [], pairs := [(2,1)], upper := (rows 113 131 28 266 144 102 102 230 358), lower := (rows 113 131 28 266 144 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 146 32 64 128 256), good := (rows 113 145 28 284 144 32 64 144 256) }] }

theorem u4057 : Upper (D 1) (R 1) [112,129,24,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4057
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4058 : Route 9 := (fun mask => (mask,id))

def c4058 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4058 : Upper (D 1) (R 1) [112,129,24,288,2] 13 := by
  apply FastRouting.sound _ _ [112,129,24,288,2] 13 (by decide) (choices 1) [2,4,64,128] r4058 c4058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1098
  · exact u1099
  · exact u1100
  · exact u1101

def b4059 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 131 28 296 20 226 194 194 450), lower := (rows 113 131 28 296 20 32 64 128 256), losses := [] }

theorem u4059 : Upper (D 1) (R 1) [112,129,24,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4059
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4060 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 28 296 80 166 198 134 390), lower := (rows 113 131 28 296 80 32 64 128 256), losses := [] }

theorem u4060 : Upper (D 1) (R 1) [112,129,24,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4060
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4061 : Route 9 := (fun mask => (mask,id))

def c4061 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4061 : Upper (D 1) (R 1) [112,129,24,288,128] 13 := by
  apply FastRouting.sound _ _ [112,129,24,288,128] 13 (by decide) (choices 1) [2,4,64] r4061 c4061
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1102
  · exact u1103
  · exact u1104

def r4062 : Route 9 := (fun mask => (mask,id))

def c4062 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4062 : Upper (D 1) (R 1) [112,129,24,384,2] 13 := by
  apply FastRouting.sound _ _ [112,129,24,384,2] 13 (by decide) (choices 1) [2,4,64] r4062 c4062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1105
  · exact u1106
  · exact u1107

def b4063 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 131 28 392 20 98 98 226 354), lower := (rows 113 131 28 392 20 32 64 128 256), losses := [] }

theorem u4063 : Upper (D 1) (R 1) [112,129,24,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4063
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4064 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 28 392 48 102 70 198 326), lower := (rows 113 131 28 392 48 32 64 128 256), losses := [] }

theorem u4064 : Upper (D 1) (R 1) [112,129,24,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4064
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4065 : PairBound 9 := { available := 116, camps := [], pairs := [(0,7)], upper := (rows 113 131 140 266 18 116 116 244 372), lower := (rows 113 131 140 266 18 32 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 8 26 36 68 0 260), good := (rows 113 19 381 282 18 32 64 0 256) }] }

theorem u4065 : Upper (D 1) (R 1) [112,129,136,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4065
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4066 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 113 131 140 266 20 114 114 242 370), lower := (rows 113 131 140 266 20 32 64 128 256), losses := [] }

theorem u4066 : Upper (D 1) (R 1) [112,129,136,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4066
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4067 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 140 266 48 118 86 214 342), lower := (rows 113 131 140 266 48 32 64 128 256), losses := [] }

theorem u4067 : Upper (D 1) (R 1) [112,129,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4067
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4068 : Route 9 := (fun mask => (mask,id))

def c4068 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4068 : Upper (D 1) (R 1) [112,129,136,272,2] 13 := by
  apply FastRouting.sound _ _ [112,129,136,272,2] 13 (by decide) (choices 1) [2,4,64] r4068 c4068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1108
  · exact u1109
  · exact u1110

def b4069 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 131 140 280 20 98 98 226 354), lower := (rows 113 131 140 280 20 32 64 128 256), losses := [] }

theorem u4069 : Upper (D 1) (R 1) [112,129,136,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4069
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4070 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 140 280 48 102 70 198 326), lower := (rows 113 131 140 280 48 32 64 128 256), losses := [] }

theorem u4070 : Upper (D 1) (R 1) [112,129,136,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4070
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4071 : PairBound 9 := { available := 108, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 148 266 18 108 108 236 364), lower := (rows 113 131 148 266 18 32 64 128 256), losses := [] }

theorem u4071 : Upper (D 1) (R 1) [112,129,144,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4071
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4072 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 131 148 266 20 106 106 234 362), lower := (rows 113 131 148 266 20 32 64 128 256), losses := [] }

theorem u4072 : Upper (D 1) (R 1) [112,129,144,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4072
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4073 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 113 131 148 266 24 102 102 230 358), lower := (rows 113 131 148 266 24 32 64 128 256), losses := [] }

theorem u4073 : Upper (D 1) (R 1) [112,129,144,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4073
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4074 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 148 266 48 110 78 206 334), lower := (rows 113 131 148 266 48 32 64 128 256), losses := [] }

theorem u4074 : Upper (D 1) (R 1) [112,129,144,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4074
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4075 : PairBound 9 := { available := 106, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 148 268 18 106 106 234 362), lower := (rows 113 131 148 268 18 32 64 128 256), losses := [] }

theorem u4075 : Upper (D 1) (R 1) [112,129,144,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4075
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4076 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 131 148 268 24 98 98 226 354), lower := (rows 113 131 148 268 24 32 64 128 256), losses := [] }

theorem u4076 : Upper (D 1) (R 1) [112,129,144,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4076
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4077 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 148 268 48 106 74 202 330), lower := (rows 113 131 148 268 48 32 64 128 256), losses := [] }

theorem u4077 : Upper (D 1) (R 1) [112,129,144,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4077
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4078 : PairBound 9 := { available := 78, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 131 148 296 18 110 78 206 334), lower := (rows 113 131 148 296 18 32 64 128 256), losses := [] }

theorem u4078 : Upper (D 1) (R 1) [112,129,144,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4078
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4079 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 131 148 296 20 106 74 202 330), lower := (rows 113 131 148 296 20 32 64 128 256), losses := [] }

theorem u4079 : Upper (D 1) (R 1) [112,129,144,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4079
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4079
end Delivery.IrregularNine14.P01
