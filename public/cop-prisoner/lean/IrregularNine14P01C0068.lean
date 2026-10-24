import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0018

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4080 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 131 148 296 24 102 70 198 326), lower := (rows 113 131 148 296 24 32 64 128 256), losses := [] }

theorem u4080 : Upper (D 1) (R 1) [112,129,144,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4080
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4081 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 148 296 80 46 78 142 270), lower := (rows 113 131 148 296 80 32 64 128 256), losses := [] }

theorem u4081 : Upper (D 1) (R 1) [112,129,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4081
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4082 : PairBound 9 := { available := 360, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 134 7 152 18 360 360 488 360), lower := (rows 113 134 7 152 18 32 64 128 256), losses := [] }

theorem u4082 : Upper (D 1) (R 1) [112,132,3,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4082
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4083 : PairBound 9 := { available := 354, camps := [], pairs := [], upper := (rows 113 134 7 152 24 354 354 482 354), lower := (rows 113 134 7 152 24 32 64 128 256), losses := [] }

theorem u4083 : Upper (D 1) (R 1) [112,132,3,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4083
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4084 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 7 152 48 362 330 458 330), lower := (rows 113 134 7 152 48 32 64 128 256), losses := [] }

theorem u4084 : Upper (D 1) (R 1) [112,132,3,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4084
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4085 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 134 7 152 272 106 106 234 362), lower := (rows 113 134 7 152 272 32 64 128 256), losses := [] }

theorem u4085 : Upper (D 1) (R 1) [112,132,3,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4085
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4086 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 7 280 18 232 232 232 488), lower := (rows 113 134 7 280 18 32 64 128 256), losses := [] }

theorem u4086 : Upper (D 1) (R 1) [112,132,3,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4086
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4087 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 134 7 280 24 226 226 226 482), lower := (rows 113 134 7 280 24 32 64 128 256), losses := [] }

theorem u4087 : Upper (D 1) (R 1) [112,132,3,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4087
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4088 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 7 280 48 234 202 202 458), lower := (rows 113 134 7 280 48 32 64 128 256), losses := [] }

theorem u4088 : Upper (D 1) (R 1) [112,132,3,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4088
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4089 : Route 9 := (fun mask => (mask,id))

def c4089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4089 : Upper (D 1) (R 1) [112,132,3,272,128] 13 := by
  apply FastRouting.sound _ _ [112,132,3,272,128] 13 (by decide) (choices 1) [2,8,64] r4089 c4089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1111
  · exact u1112
  · exact u1113

def b4090 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 489, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 7 392 18 120 120 248 376), lower := (rows 113 134 7 392 18 32 64 128 256), losses := [] }

theorem u4090 : Upper (D 1) (R 1) [112,132,3,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4090
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4091 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 113 134 7 392 24 114 114 242 370), lower := (rows 113 134 7 392 24 32 64 128 256), losses := [] }

theorem u4091 : Upper (D 1) (R 1) [112,132,3,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4091
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4092 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 7 392 48 122 90 218 346), lower := (rows 113 134 7 392 48 32 64 128 256), losses := [] }

theorem u4092 : Upper (D 1) (R 1) [112,132,3,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4092
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4093 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 13 266 18 240 240 240 496), lower := (rows 113 134 13 266 18 32 64 128 256), losses := [] }

theorem u4093 : Upper (D 1) (R 1) [112,132,9,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4093
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4094 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 13 266 48 242 210 210 466), lower := (rows 113 134 13 266 48 32 64 128 256), losses := [] }

theorem u4094 : Upper (D 1) (R 1) [112,132,9,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4094
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4095_2 : Upper (D 1) (R 1) [112,132,9,258,128,2] 13 :=
  permutation_upper _ _ _ [112,132,9,258,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1114

theorem m4095_16 : Upper (D 1) (R 1) [112,132,9,258,128,16] 13 :=
  permutation_upper _ _ _ [112,132,9,258,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1115

theorem m4095_64 : Upper (D 1) (R 1) [112,132,9,258,128,64] 13 :=
  permutation_upper _ _ _ [112,132,9,258,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1116

def r4095 : Route 9 := (fun mask => (mask,id))

def c4095 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4095 : Upper (D 1) (R 1) [112,132,9,258,128] 13 := by
  apply FastRouting.sound _ _ [112,132,9,258,128] 13 (by decide) (choices 1) [2,16,64] r4095 c4095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4095_2
  · exact m4095_16
  · exact m4095_64

def b4096 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 14 265 18 240 240 240 496), lower := (rows 113 134 14 265 18 32 64 128 256), losses := [] }

theorem u4096 : Upper (D 1) (R 1) [112,132,10,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4096
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4097 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 14 265 48 242 210 210 466), lower := (rows 113 134 14 265 48 32 64 128 256), losses := [] }

theorem u4097 : Upper (D 1) (R 1) [112,132,10,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4097
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4098_2 : Upper (D 1) (R 1) [112,132,10,257,128,2] 13 :=
  permutation_upper _ _ _ [112,132,10,257,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1117

theorem m4098_16 : Upper (D 1) (R 1) [112,132,10,257,128,16] 13 :=
  permutation_upper _ _ _ [112,132,10,257,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1118

theorem m4098_64 : Upper (D 1) (R 1) [112,132,10,257,128,64] 13 :=
  permutation_upper _ _ _ [112,132,10,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1119

def r4098 : Route 9 := (fun mask => (mask,id))

def c4098 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4098 : Upper (D 1) (R 1) [112,132,10,257,128] 13 := by
  apply FastRouting.sound _ _ [112,132,10,257,128] 13 (by decide) (choices 1) [2,16,64] r4098 c4098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4098_2
  · exact m4098_16
  · exact m4098_64

def b4099 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 134 14 280 17 226 226 226 482), lower := (rows 113 134 14 280 17 32 64 128 256), losses := [] }

theorem u4099 : Upper (D 1) (R 1) [112,132,10,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4099
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4100 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 14 280 18 225 225 225 481), lower := (rows 113 134 14 280 18 32 64 128 256), losses := [] }

theorem u4100 : Upper (D 1) (R 1) [112,132,10,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4100
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4101 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 14 280 48 227 195 195 451), lower := (rows 113 134 14 280 48 32 64 128 256), losses := [] }

theorem u4101 : Upper (D 1) (R 1) [112,132,10,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4101
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4102 : Route 9 := (fun mask => (mask,id))

def c4102 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4102 : Upper (D 1) (R 1) [112,132,10,272,128] 13 := by
  apply FastRouting.sound _ _ [112,132,10,272,128] 13 (by decide) (choices 1) [1,2,64] r4102 c4102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1120
  · exact u1121
  · exact u1122

def b4103 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 22 137 18 360 360 488 360), lower := (rows 113 134 22 137 18 32 64 128 256), losses := [] }

theorem u4103 : Upper (D 1) (R 1) [112,132,18,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4103
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4104 : PairBound 9 := { available := 354, camps := [], pairs := [], upper := (rows 113 134 22 137 24 354 354 482 354), lower := (rows 113 134 22 137 24 32 64 128 256), losses := [] }

theorem u4104 : Upper (D 1) (R 1) [112,132,18,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4104
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4105 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 22 137 48 362 330 458 330), lower := (rows 113 134 22 137 48 32 64 128 256), losses := [] }

theorem u4105 : Upper (D 1) (R 1) [112,132,18,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4105
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4106 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 134 22 137 272 106 106 234 362), lower := (rows 113 134 22 137 272 32 64 128 256), losses := [] }

theorem u4106 : Upper (D 1) (R 1) [112,132,18,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4106
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4107 : PairBound 9 := { available := 330, camps := [], pairs := [], upper := (rows 113 134 22 168 17 362 330 458 330), lower := (rows 113 134 22 168 17 32 64 128 256), losses := [] }

theorem u4107 : Upper (D 1) (R 1) [112,132,18,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4107
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4108 : PairBound 9 := { available := 329, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 22 168 18 361 329 457 329), lower := (rows 113 134 22 168 18 32 64 128 256), losses := [] }

theorem u4108 : Upper (D 1) (R 1) [112,132,18,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4108
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4109 : PairBound 9 := { available := 323, camps := [], pairs := [], upper := (rows 113 134 22 168 24 355 323 451 323), lower := (rows 113 134 22 168 24 32 64 128 256), losses := [] }

theorem u4109 : Upper (D 1) (R 1) [112,132,18,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4109
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4110 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 22 168 80 299 331 395 267), lower := (rows 113 134 22 168 80 32 64 128 256), losses := [] }

theorem u4110 : Upper (D 1) (R 1) [112,132,18,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4110
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4111 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 113 134 22 168 272 107 75 203 331), lower := (rows 113 134 22 168 272 32 64 128 256), losses := [] }

theorem u4111 : Upper (D 1) (R 1) [112,132,18,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4111
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4112 : PairBound 9 := { available := 232, camps := [{ cop := 7, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 22 265 18 232 232 232 488), lower := (rows 113 134 22 265 18 32 64 128 256), losses := [] }

theorem u4112 : Upper (D 1) (R 1) [112,132,18,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4112
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4113 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 134 22 265 24 226 226 226 482), lower := (rows 113 134 22 265 24 32 64 128 256), losses := [] }

theorem u4113 : Upper (D 1) (R 1) [112,132,18,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4113
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4114 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 22 265 48 234 202 202 458), lower := (rows 113 134 22 265 48 32 64 128 256), losses := [] }

theorem u4114 : Upper (D 1) (R 1) [112,132,18,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4114
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4115 : PairBound 9 := { available := 106, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 22 265 144 106 106 234 362), lower := (rows 113 134 22 265 144 32 64 128 256), losses := [] }

theorem u4115 : Upper (D 1) (R 1) [112,132,18,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4115
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4116 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 113 134 22 296 17 234 202 202 458), lower := (rows 113 134 22 296 17 32 64 128 256), losses := [] }

theorem u4116 : Upper (D 1) (R 1) [112,132,18,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4116
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4117 : PairBound 9 := { available := 201, camps := [{ cop := 7, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 22 296 18 233 201 201 457), lower := (rows 113 134 22 296 18 32 64 128 256), losses := [] }

theorem u4117 : Upper (D 1) (R 1) [112,132,18,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4117
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4118 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 134 22 296 24 227 195 195 451), lower := (rows 113 134 22 296 24 32 64 128 256), losses := [] }

theorem u4118 : Upper (D 1) (R 1) [112,132,18,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4118
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4119 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 22 296 80 171 203 139 395), lower := (rows 113 134 22 296 80 32 64 128 256), losses := [] }

theorem u4119 : Upper (D 1) (R 1) [112,132,18,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4119
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4120 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 22 296 144 107 75 203 331), lower := (rows 113 134 22 296 144 32 64 128 256), losses := [] }

theorem u4120 : Upper (D 1) (R 1) [112,132,18,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4120
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4121 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 134 22 392 17 106 106 234 362), lower := (rows 113 134 22 392 17 32 64 128 256), losses := [] }

theorem u4121 : Upper (D 1) (R 1) [112,132,18,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4121
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4122 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 22 392 18 105 105 233 361), lower := (rows 113 134 22 392 18 32 64 128 256), losses := [] }

theorem u4122 : Upper (D 1) (R 1) [112,132,18,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4122
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4123 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 113 134 22 392 24 99 99 227 355), lower := (rows 113 134 22 392 24 32 64 128 256), losses := [] }

theorem u4123 : Upper (D 1) (R 1) [112,132,18,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4123
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4124 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 22 392 48 107 75 203 331), lower := (rows 113 134 22 392 48 32 64 128 256), losses := [] }

theorem u4124 : Upper (D 1) (R 1) [112,132,18,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4124
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4125 : PairBound 9 := { available := 450, camps := [], pairs := [], upper := (rows 113 134 28 42 17 482 450 450 450), lower := (rows 113 134 28 42 17 32 64 128 256), losses := [] }

theorem u4125 : Upper (D 1) (R 1) [112,132,24,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4125
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4126 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 134 28 42 18 481 449 449 449), lower := (rows 113 134 28 42 18 32 64 128 256), losses := [] }

theorem u4126 : Upper (D 1) (R 1) [112,132,24,34,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4126
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4127 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 28 42 80 419 451 387 387), lower := (rows 113 134 28 42 80 32 64 128 256), losses := [] }

theorem u4127 : Upper (D 1) (R 1) [112,132,24,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4127
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4128 : PairBound 9 := { available := 323, camps := [], pairs := [(2,1)], upper := (rows 113 134 28 42 144 355 323 451 323), lower := (rows 113 134 28 42 144 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 146 32 64 128 256), good := (rows 113 148 28 60 144 32 64 144 256) }] }

theorem u4128 : Upper (D 1) (R 1) [112,132,24,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4128
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4129 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 113 134 28 42 272 227 195 195 451), lower := (rows 113 134 28 42 272 32 64 128 256), losses := [] }

theorem u4129 : Upper (D 1) (R 1) [112,132,24,34,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4129
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4130 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 134 28 266 17 226 226 226 482), lower := (rows 113 134 28 266 17 32 64 128 256), losses := [] }

theorem u4130 : Upper (D 1) (R 1) [112,132,24,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4130
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4131 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 134 28 266 18 225 225 225 481), lower := (rows 113 134 28 266 18 32 64 128 256), losses := [] }

theorem u4131 : Upper (D 1) (R 1) [112,132,24,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4131
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4132 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 28 266 48 227 195 195 451), lower := (rows 113 134 28 266 48 32 64 128 256), losses := [] }

theorem u4132 : Upper (D 1) (R 1) [112,132,24,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4132
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4133 : PairBound 9 := { available := 99, camps := [], pairs := [(2,1)], upper := (rows 113 134 28 266 144 99 99 227 355), lower := (rows 113 134 28 266 144 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 146 32 64 128 256), good := (rows 113 148 28 284 144 32 64 144 256) }] }

theorem u4133 : Upper (D 1) (R 1) [112,132,24,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4133
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4134 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 134 28 296 17 226 194 194 450), lower := (rows 113 134 28 296 17 32 64 128 256), losses := [] }

theorem u4134 : Upper (D 1) (R 1) [112,132,24,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4134
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4135 : Route 9 := (fun mask => (mask,id))

def c4135 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4135 : Upper (D 1) (R 1) [112,132,24,288,2] 13 := by
  apply FastRouting.sound _ _ [112,132,24,288,2] 13 (by decide) (choices 1) [1,2,64,128] r4135 c4135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1123
  · exact u1124
  · exact u1125
  · exact u1126

def b4136 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 28 296 80 163 195 131 387), lower := (rows 113 134 28 296 80 32 64 128 256), losses := [] }

theorem u4136 : Upper (D 1) (R 1) [112,132,24,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4136
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4137 : Route 9 := (fun mask => (mask,id))

def c4137 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4137 : Upper (D 1) (R 1) [112,132,24,288,128] 13 := by
  apply FastRouting.sound _ _ [112,132,24,288,128] 13 (by decide) (choices 1) [1,2,64] r4137 c4137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1127
  · exact u1128
  · exact u1129

def b4138 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 134 261 26 18 232 232 232 488), lower := (rows 113 134 261 26 18 32 64 128 256), losses := [] }

theorem u4138 : Upper (D 1) (R 1) [112,132,257,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4138
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4139 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 113 134 261 26 24 226 226 226 482), lower := (rows 113 134 261 26 24 32 64 128 256), losses := [] }

theorem u4139 : Upper (D 1) (R 1) [112,132,257,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4139
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4139
end Delivery.IrregularNine14.P01
