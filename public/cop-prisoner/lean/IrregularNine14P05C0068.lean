import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0023

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4080 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 265 52 40 99 163 291), lower := (rows 19 70 140 265 52 40 64 128 256), losses := [] }

theorem u4080 : Upper (D 5) (R 5) [18,68,136,257,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4080
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4081 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 140 265 56 33 102 166 294), lower := (rows 19 70 140 265 56 33 64 128 256), losses := [] }

theorem u4081 : Upper (D 5) (R 5) [18,68,136,257,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4081
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4082 : PairBound 9 := { available := 37, camps := [], pairs := [(4,0),(4,2)], upper := (rows 19 70 140 265 56 34 101 165 293), lower := (rows 19 70 140 265 56 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 35 64 128 256), good := (rows 50 102 156 312 56 34 64 128 256) },{ target := 2, region := (rows 1 2 0 8 24 35 64 128 256), good := (rows 51 98 152 313 56 34 64 128 256) }] }

theorem u4082 : Upper (D 5) (R 5) [18,68,136,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4082
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4083 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 265 56 36 99 163 291), lower := (rows 19 70 140 265 56 36 64 128 256), losses := [] }

theorem u4083 : Upper (D 5) (R 5) [18,68,136,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4083
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4084 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 266 49 33 108 172 300), lower := (rows 19 70 140 266 49 33 64 128 256), losses := [] }

theorem u4084 : Upper (D 5) (R 5) [18,68,136,258,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4084
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4085 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 140 266 49 36 105 169 297), lower := (rows 19 70 140 266 49 36 64 128 256), losses := [] }

theorem u4085 : Upper (D 5) (R 5) [18,68,136,258,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4085
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4086 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 140 266 49 40 101 165 293), lower := (rows 19 70 140 266 49 40 64 128 256), losses := [] }

theorem u4086 : Upper (D 5) (R 5) [18,68,136,258,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4086
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4087 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 140 266 52 33 105 169 297), lower := (rows 19 70 140 266 52 33 64 128 256), losses := [] }

theorem u4087 : Upper (D 5) (R 5) [18,68,136,258,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4087
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4088 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 266 52 40 97 161 289), lower := (rows 19 70 140 266 52 40 64 128 256), losses := [] }

theorem u4088 : Upper (D 5) (R 5) [18,68,136,258,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4088
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4089 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 140 266 56 33 101 165 293), lower := (rows 19 70 140 266 56 33 64 128 256), losses := [] }

theorem u4089 : Upper (D 5) (R 5) [18,68,136,258,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4089
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4090 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 140 266 56 36 97 161 289), lower := (rows 19 70 140 266 56 36 64 128 256), losses := [] }

theorem u4090 : Upper (D 5) (R 5) [18,68,136,258,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4090
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4091 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 268 25 33 98 162 290), lower := (rows 19 70 140 268 25 33 64 128 256), losses := [] }

theorem u4091 : Upper (D 5) (R 5) [18,68,136,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4091
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4092 : Route 9 := (fun mask => (mask,id))

def c4092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4092 : Upper (D 5) (R 5) [18,68,136,260,9,2] 13 := by
  apply FastRouting.sound _ _ [18,68,136,260,9,2] 13 (by decide) (choices 1) [1,32] r4092 c4092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1386
  · exact u1387

def b4093 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 268 49 33 106 170 298), lower := (rows 19 70 140 268 49 33 64 128 256), losses := [] }

theorem u4093 : Upper (D 5) (R 5) [18,68,136,260,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4093
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4094 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 268 49 34 105 169 297), lower := (rows 19 70 140 268 49 34 64 128 256), losses := [] }

theorem u4094 : Upper (D 5) (R 5) [18,68,136,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4094
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4095 : PairBound 9 := { available := 35, camps := [], pairs := [(0,2),(4,2)], upper := (rows 19 70 140 268 49 40 99 163 291), lower := (rows 19 70 140 268 49 40 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 18 44 66 130 258), good := (rows 467 499 168 296 49 40 64 128 256) }] }

theorem u4095 : Upper (D 5) (R 5) [18,68,136,260,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4095
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4096 : Route 9 := (fun mask => (mask,id))

def c4096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4096 : Upper (D 5) (R 5) [18,68,136,260,40,1] 13 := by
  apply FastRouting.sound _ _ [18,68,136,260,40,1] 13 (by decide) (choices 1) [1,2,32] r4096 c4096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1388
  · exact u1389
  · exact u1390

def r4097 : Route 9 := (fun mask => (mask,id))

def c4097 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4097 : Upper (D 5) (R 5) [18,68,136,260,40,2] 13 := by
  apply FastRouting.sound _ _ [18,68,136,260,40,2] 13 (by decide) (choices 1) [1,32] r4097 c4097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1391
  · exact u1392

def b4098 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 140 296 25 33 102 166 294), lower := (rows 19 70 140 296 25 33 64 128 256), losses := [] }

theorem u4098 : Upper (D 5) (R 5) [18,68,136,288,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4098
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4099 : Route 9 := (fun mask => (mask,id))

def c4099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4099 : Upper (D 5) (R 5) [18,68,136,288,9,2] 13 := by
  apply FastRouting.sound _ _ [18,68,136,288,9,2] 13 (by decide) (choices 1) [1,4,32] r4099 c4099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1393
  · exact u1394
  · exact u1395

def r4100 : Route 9 := (fun mask => (mask,id))

def c4100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4100 : Upper (D 5) (R 5) [18,68,136,288,9,4] 13 := by
  apply FastRouting.sound _ _ [18,68,136,288,9,4] 13 (by decide) (choices 1) [1,2,32] r4100 c4100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1396
  · exact u1397
  · exact u1398

def b4101 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 296 49 33 78 142 270), lower := (rows 19 70 140 296 49 33 64 128 256), losses := [] }

theorem u4101 : Upper (D 5) (R 5) [18,68,136,288,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4101
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4102 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 140 296 49 34 77 141 269), lower := (rows 19 70 140 296 49 34 64 128 256), losses := [] }

theorem u4102 : Upper (D 5) (R 5) [18,68,136,288,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4102
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4103 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 140 296 49 36 75 139 267), lower := (rows 19 70 140 296 49 36 64 128 256), losses := [] }

theorem u4103 : Upper (D 5) (R 5) [18,68,136,288,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4103
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4104 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 140 296 49 40 71 135 263), lower := (rows 19 70 140 296 49 40 64 128 256), losses := [] }

theorem u4104 : Upper (D 5) (R 5) [18,68,136,288,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4104
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4105 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 140 296 52 33 75 139 267), lower := (rows 19 70 140 296 52 33 64 128 256), losses := [] }

theorem u4105 : Upper (D 5) (R 5) [18,68,136,288,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4105
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4106 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 49, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 140 296 52 34 73 137 265), lower := (rows 19 70 140 296 52 34 64 128 256), losses := [] }

theorem u4106 : Upper (D 5) (R 5) [18,68,136,288,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4106
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4107 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 140 296 52 40 67 131 259), lower := (rows 19 70 140 296 52 40 64 128 256), losses := [] }

theorem u4107 : Upper (D 5) (R 5) [18,68,136,288,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4107
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4108 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 164 41 276 33 74 138 266), lower := (rows 19 70 164 41 276 33 64 128 256), losses := [] }

theorem u4108 : Upper (D 5) (R 5) [18,68,160,33,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4108
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4109 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 19 70 164 41 276 34 73 137 265), lower := (rows 19 70 164 41 276 34 64 128 256), losses := [] }

theorem u4109 : Upper (D 5) (R 5) [18,68,160,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4109
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4110 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 40, targets := 2 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 164 41 276 40 75 139 267), lower := (rows 19 70 164 41 276 40 64 128 256), losses := [] }

theorem u4110 : Upper (D 5) (R 5) [18,68,160,33,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4110
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4111 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 164 41 280 33 78 142 270), lower := (rows 19 70 164 41 280 33 64 128 256), losses := [] }

theorem u4111 : Upper (D 5) (R 5) [18,68,160,33,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4111
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4112 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 19 70 164 41 280 34 77 141 269), lower := (rows 19 70 164 41 280 34 64 128 256), losses := [] }

theorem u4112 : Upper (D 5) (R 5) [18,68,160,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4112
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4113 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 164 41 280 36 75 139 267), lower := (rows 19 70 164 41 280 36 64 128 256), losses := [] }

theorem u4113 : Upper (D 5) (R 5) [18,68,160,33,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4113
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4114 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 164 41 280 40 71 135 263), lower := (rows 19 70 164 41 280 40 64 128 256), losses := [] }

theorem u4114 : Upper (D 5) (R 5) [18,68,160,33,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4114
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4115 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 164 42 273 33 76 140 268), lower := (rows 19 70 164 42 273 33 64 128 256), losses := [] }

theorem u4115 : Upper (D 5) (R 5) [18,68,160,34,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4115
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4116 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 273, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 164 42 273 36 73 137 265), lower := (rows 19 70 164 42 273 36 64 128 256), losses := [] }

theorem u4116 : Upper (D 5) (R 5) [18,68,160,34,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4116
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4117 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 70 164 42 273 40 77 141 269), lower := (rows 19 70 164 42 273 40 64 128 256), losses := [] }

theorem u4117 : Upper (D 5) (R 5) [18,68,160,34,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4117
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4118 : Route 9 := (fun mask => (mask,id))

def c4118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4118 : Upper (D 5) (R 5) [18,68,160,34,260,1] 13 := by
  apply FastRouting.sound _ _ [18,68,160,34,260,1] 13 (by decide) (choices 1) [1,8] r4118 c4118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1399
  · exact u1400

def b4119 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 70 164 42 276 40 73 137 265), lower := (rows 19 70 164 42 276 40 64 128 256), losses := [] }

theorem u4119 : Upper (D 5) (R 5) [18,68,160,34,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4119
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4120 : Route 9 := (fun mask => (mask,id))

def c4120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4120 : Upper (D 5) (R 5) [18,68,160,34,264,1] 13 := by
  apply FastRouting.sound _ _ [18,68,160,34,264,1] 13 (by decide) (choices 1) [1,4,8] r4120 c4120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1401
  · exact u1402
  · exact u1403

def b4121 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 273, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 164 42 280 36 73 137 265), lower := (rows 19 70 164 42 280 36 64 128 256), losses := [] }

theorem u4121 : Upper (D 5) (R 5) [18,68,160,34,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4121
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4122 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 70 164 42 280 40 69 133 261), lower := (rows 19 70 164 42 280 40 64 128 256), losses := [] }

theorem u4122 : Upper (D 5) (R 5) [18,68,160,34,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4122
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4123 : Route 9 := (fun mask => (mask,id))

def c4123 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4123 : Upper (D 5) (R 5) [18,68,160,257,12,1] 13 := by
  apply FastRouting.sound _ _ [18,68,160,257,12,1] 13 (by decide) (choices 1) [2,8,32] r4123 c4123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1404
  · exact u1405
  · exact u1406

def r4124 : Route 9 := (fun mask => (mask,id))

def c4124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4124 : Upper (D 5) (R 5) [18,68,160,257,12,2] 13 := by
  apply FastRouting.sound _ _ [18,68,160,257,12,2] 13 (by decide) (choices 1) [1,8,32] r4124 c4124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1407
  · exact u1408
  · exact u1409

def r4125 : Route 9 := (fun mask => (mask,id))

def c4125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4125 : Upper (D 5) (R 5) [18,68,160,257,12,8] 13 := by
  apply FastRouting.sound _ _ [18,68,160,257,12,8] 13 (by decide) (choices 1) [1,2,32] r4125 c4125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1410
  · exact u1411
  · exact u1412

def b4126 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 164 265 56 33 78 142 270), lower := (rows 19 70 164 265 56 33 64 128 256), losses := [] }

theorem u4126 : Upper (D 5) (R 5) [18,68,160,257,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4126
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4127 : PairBound 9 := { available := 13, camps := [], pairs := [(4,0),(4,2)], upper := (rows 19 70 164 265 56 34 77 141 269), lower := (rows 19 70 164 265 56 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 35 64 128 256), good := (rows 50 102 164 312 56 34 64 128 256) },{ target := 2, region := (rows 1 2 0 8 24 35 64 128 256), good := (rows 51 98 160 313 56 34 64 128 256) }] }

theorem u4127 : Upper (D 5) (R 5) [18,68,160,257,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4127
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4128 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 164 265 56 36 75 139 267), lower := (rows 19 70 164 265 56 36 64 128 256), losses := [] }

theorem u4128 : Upper (D 5) (R 5) [18,68,160,257,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4128
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4129 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 164 265 56 40 71 135 263), lower := (rows 19 70 164 265 56 40 64 128 256), losses := [] }

theorem u4129 : Upper (D 5) (R 5) [18,68,160,257,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4129
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4130 : Route 9 := (fun mask => (mask,id))

def c4130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4130 : Upper (D 5) (R 5) [18,68,160,258,12,1] 13 := by
  apply FastRouting.sound _ _ [18,68,160,258,12,1] 13 (by decide) (choices 1) [1,8,32] r4130 c4130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1413
  · exact u1414
  · exact u1415

def b4131 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(2,1),(3,2)], upper := (rows 19 70 164 266 28 40 97 161 289), lower := (rows 19 70 164 266 28 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 56 65 129 257), good := (rows 501 68 164 296 60 40 64 128 256) }] }

theorem u4131 : Upper (D 5) (R 5) [18,68,160,258,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4131
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4132 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 49, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 70 164 266 49 33 76 140 268), lower := (rows 19 70 164 266 49 33 64 128 256), losses := [] }

theorem u4132 : Upper (D 5) (R 5) [18,68,160,258,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4132
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4133 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 164 266 49 36 73 137 265), lower := (rows 19 70 164 266 49 36 64 128 256), losses := [] }

theorem u4133 : Upper (D 5) (R 5) [18,68,160,258,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4133
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4134 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 164 266 49 40 77 141 269), lower := (rows 19 70 164 266 49 40 64 128 256), losses := [] }

theorem u4134 : Upper (D 5) (R 5) [18,68,160,258,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4134
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4135 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 19 70 164 266 56 33 77 141 269), lower := (rows 19 70 164 266 56 33 64 128 256), losses := [] }

theorem u4135 : Upper (D 5) (R 5) [18,68,160,258,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4135
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4136 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 70 164 266 56 36 73 137 265), lower := (rows 19 70 164 266 56 36 64 128 256), losses := [] }

theorem u4136 : Upper (D 5) (R 5) [18,68,160,258,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4136
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4137 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 199, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 164 266 56 40 69 133 261), lower := (rows 19 70 164 266 56 40 64 128 256), losses := [] }

theorem u4137 : Upper (D 5) (R 5) [18,68,160,258,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4137
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4138 : PairBound 9 := { available := 42, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 164 268 25 33 106 170 298), lower := (rows 19 70 164 268 25 33 64 128 256), losses := [] }

theorem u4138 : Upper (D 5) (R 5) [18,68,160,260,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4138
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4139 : Route 9 := (fun mask => (mask,id))

def c4139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4139 : Upper (D 5) (R 5) [18,68,160,260,9,2] 13 := by
  apply FastRouting.sound _ _ [18,68,160,260,9,2] 13 (by decide) (choices 1) [1,8,32] r4139 c4139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1416
  · exact u1417
  · exact u1418

#print axioms u4139
end Delivery.IrregularNine14.P05
