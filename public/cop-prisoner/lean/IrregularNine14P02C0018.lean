import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P02C0007
import IrregularNine14P02C0008

namespace Delivery.IrregularNine14.P02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1080 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 140 266 17 480 480 480 480), lower := (rows 113 22 140 266 17 32 64 128 256), losses := [] }

theorem u1080 : Upper (D 2) (R 2) [112,20,136,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1080
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1081 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 22 140 266 48 481 449 449 449), lower := (rows 113 22 140 266 48 32 64 128 256), losses := [] }

theorem u1081 : Upper (D 2) (R 2) [112,20,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1081
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1082 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 140 266 144 353 353 481 353), lower := (rows 113 22 140 266 144 32 64 128 256), losses := [] }

theorem u1082 : Upper (D 2) (R 2) [112,20,136,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1082
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1083 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 225, targets := 256 }], pairs := [(0,8),(1,5)], upper := (rows 113 22 140 266 272 225 225 225 481), lower := (rows 113 22 140 266 272 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 280 0 64 128 256), good := (rows 81 22 158 282 272 0 64 128 272) }] }

theorem u1083 : Upper (D 2) (R 2) [112,20,136,258,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1083
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1084 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 140 296 17 482 450 450 450), lower := (rows 113 22 140 296 17 32 64 128 256), losses := [] }

theorem u1084 : Upper (D 2) (R 2) [112,20,136,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1084
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1085 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 140 296 18 481 449 449 449), lower := (rows 113 22 140 296 18 32 64 128 256), losses := [] }

theorem u1085 : Upper (D 2) (R 2) [112,20,136,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1085
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1086 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 140 296 80 419 451 387 387), lower := (rows 113 22 140 296 80 32 64 128 256), losses := [] }

theorem u1086 : Upper (D 2) (R 2) [112,20,136,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1086
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1087 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 140 296 144 355 323 451 323), lower := (rows 113 22 140 296 144 32 64 128 256), losses := [] }

theorem u1087 : Upper (D 2) (R 2) [112,20,136,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1087
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1088 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 225, targets := 256 }], pairs := [(0,8),(1,5)], upper := (rows 113 22 140 296 272 227 195 195 451), lower := (rows 113 22 140 296 272 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 280 0 64 128 256), good := (rows 81 22 158 280 272 0 64 128 272) }] }

theorem u1088 : Upper (D 2) (R 2) [112,20,136,288,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1088
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1089 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 137 18 360 328 456 328), lower := (rows 113 22 164 137 18 32 64 128 256), losses := [] }

theorem u1089 : Upper (D 2) (R 2) [112,20,160,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1089
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1090 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 137 24 354 322 450 322), lower := (rows 113 22 164 137 24 32 64 128 256), losses := [] }

theorem u1090 : Upper (D 2) (R 2) [112,20,160,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1090
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1091 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 164 137 80 298 330 394 266), lower := (rows 113 22 164 137 80 32 64 128 256), losses := [] }

theorem u1091 : Upper (D 2) (R 2) [112,20,160,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1091
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1092 : Route 9 := (fun mask => (mask,id))

def c1092 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1092 : Upper (D 2) (R 2) [112,20,160,129,256] 13 := by
  apply FastRouting.sound _ _ [112,20,160,129,256] 13 (by decide) (choices 1) [2,8,64,256] r1092 c1092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u454
  · exact u455
  · exact u456
  · exact u457

def b1093 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 138 17 360 328 456 328), lower := (rows 113 22 164 138 17 32 64 128 256), losses := [] }

theorem u1093 : Upper (D 2) (R 2) [112,20,160,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1093
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1094 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 138 24 353 321 449 321), lower := (rows 113 22 164 138 24 32 64 128 256), losses := [] }

theorem u1094 : Upper (D 2) (R 2) [112,20,160,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1094
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1095 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 164 138 80 297 329 393 265), lower := (rows 113 22 164 138 80 32 64 128 256), losses := [] }

theorem u1095 : Upper (D 2) (R 2) [112,20,160,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1095
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1096 : Route 9 := (fun mask => (mask,id))

def c1096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1096 : Upper (D 2) (R 2) [112,20,160,130,256] 13 := by
  apply FastRouting.sound _ _ [112,20,160,130,256] 13 (by decide) (choices 1) [1,8,64,256] r1096 c1096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u458
  · exact u459
  · exact u460
  · exact u461

def b1097 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 200 17 298 330 394 266), lower := (rows 113 22 164 200 17 32 64 128 256), losses := [] }

theorem u1097 : Upper (D 2) (R 2) [112,20,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1097
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1098 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 200 18 297 329 393 265), lower := (rows 113 22 164 200 18 32 64 128 256), losses := [] }

theorem u1098 : Upper (D 2) (R 2) [112,20,160,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1098
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1099 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 200 24 291 323 387 259), lower := (rows 113 22 164 200 24 32 64 128 256), losses := [] }

theorem u1099 : Upper (D 2) (R 2) [112,20,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1099
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1100 : Route 9 := (fun mask => (mask,id))

def c1100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1100 : Upper (D 2) (R 2) [112,20,160,192,256] 13 := by
  apply FastRouting.sound _ _ [112,20,160,192,256] 13 (by decide) (choices 1) [1,2,8,256] r1100 c1100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u462
  · exact u463
  · exact u464
  · exact u465

def b1101 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 265 18 488 456 456 456), lower := (rows 113 22 164 265 18 32 64 128 256), losses := [] }

theorem u1101 : Upper (D 2) (R 2) [112,20,160,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1101
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1102 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 265 24 482 450 450 450), lower := (rows 113 22 164 265 24 32 64 128 256), losses := [] }

theorem u1102 : Upper (D 2) (R 2) [112,20,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1102
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1103 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 164 265 80 426 458 394 394), lower := (rows 113 22 164 265 80 32 64 128 256), losses := [] }

theorem u1103 : Upper (D 2) (R 2) [112,20,160,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1103
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1104 : PairBound 9 := { available := 330, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 164 265 144 362 330 458 330), lower := (rows 113 22 164 265 144 32 64 128 256), losses := [] }

theorem u1104 : Upper (D 2) (R 2) [112,20,160,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1104
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1105 : Route 9 := (fun mask => (mask,id))

def c1105 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1105 : Upper (D 2) (R 2) [112,20,160,257,256] 13 := by
  apply FastRouting.sound _ _ [112,20,160,257,256] 13 (by decide) (choices 1) [2,8,64,128] r1105 c1105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u466
  · exact u467
  · exact u468
  · exact u469

def b1106 : PairBound 9 := { available := 456, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 266 17 488 456 456 456), lower := (rows 113 22 164 266 17 32 64 128 256), losses := [] }

theorem u1106 : Upper (D 2) (R 2) [112,20,160,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1106
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1107 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 388, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 266 24 481 449 449 449), lower := (rows 113 22 164 266 24 32 64 128 256), losses := [] }

theorem u1107 : Upper (D 2) (R 2) [112,20,160,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1107
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1108 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 164 266 80 425 457 393 393), lower := (rows 113 22 164 266 80 32 64 128 256), losses := [] }

theorem u1108 : Upper (D 2) (R 2) [112,20,160,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1108
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1109 : PairBound 9 := { available := 329, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 164 266 144 361 329 457 329), lower := (rows 113 22 164 266 144 32 64 128 256), losses := [] }

theorem u1109 : Upper (D 2) (R 2) [112,20,160,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1109
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1110 : Route 9 := (fun mask => (mask,id))

def c1110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1110 : Upper (D 2) (R 2) [112,20,160,258,256] 13 := by
  apply FastRouting.sound _ _ [112,20,160,258,256] 13 (by decide) (choices 1) [1,8,64,128] r1110 c1110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u470
  · exact u471
  · exact u472
  · exact u473

def b1111 : PairBound 9 := { available := 394, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 328 17 426 458 394 394), lower := (rows 113 22 164 328 17 32 64 128 256), losses := [] }

theorem u1111 : Upper (D 2) (R 2) [112,20,160,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1111
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1112 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 328 18 425 457 393 393), lower := (rows 113 22 164 328 18 32 64 128 256), losses := [] }

theorem u1112 : Upper (D 2) (R 2) [112,20,160,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1112
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1113 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 164 328 24 419 451 387 387), lower := (rows 113 22 164 328 24 32 64 128 256), losses := [] }

theorem u1113 : Upper (D 2) (R 2) [112,20,160,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1113
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1114 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 164 328 144 299 331 395 267), lower := (rows 113 22 164 328 144 32 64 128 256), losses := [] }

theorem u1114 : Upper (D 2) (R 2) [112,20,160,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1114
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1115 : Route 9 := (fun mask => (mask,id))

def c1115 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1115 : Upper (D 2) (R 2) [112,20,160,320,256] 13 := by
  apply FastRouting.sound _ _ [112,20,160,320,256] 13 (by decide) (choices 1) [1,2,8,128] r1115 c1115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u474
  · exact u475
  · exact u476
  · exact u477

def b1116 : PairBound 9 := { available := 330, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 164 392 17 362 330 458 330), lower := (rows 113 22 164 392 17 32 64 128 256), losses := [] }

theorem u1116 : Upper (D 2) (R 2) [112,20,160,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1116
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1117 : PairBound 9 := { available := 329, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 164 392 18 361 329 457 329), lower := (rows 113 22 164 392 18 32 64 128 256), losses := [] }

theorem u1117 : Upper (D 2) (R 2) [112,20,160,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1117
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1118 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 113 22 164 392 24 355 323 451 323), lower := (rows 113 22 164 392 24 32 64 128 256), losses := [] }

theorem u1118 : Upper (D 2) (R 2) [112,20,160,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1118
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1119 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 164 392 80 299 331 395 267), lower := (rows 113 22 164 392 80 32 64 128 256), losses := [] }

theorem u1119 : Upper (D 2) (R 2) [112,20,160,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1119
    (constants 2).1 (constants 2).2 (by decide +kernel)

def r1120 : Route 9 := (fun mask => (mask,id))

def c1120 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1120 : Upper (D 2) (R 2) [112,20,160,384,256] 13 := by
  apply FastRouting.sound _ _ [112,20,160,384,256] 13 (by decide) (choices 1) [1,2,8,64] r1120 c1120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u478
  · exact u479
  · exact u480
  · exact u481

def b1121 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 388 137 18 360 360 488 360), lower := (rows 113 22 388 137 18 32 64 128 256), losses := [] }

theorem u1121 : Upper (D 2) (R 2) [112,20,384,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1121
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1122 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 388 137 24 354 354 482 354), lower := (rows 113 22 388 137 24 32 64 128 256), losses := [] }

theorem u1122 : Upper (D 2) (R 2) [112,20,384,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1122
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1123 : PairBound 9 := { available := 330, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 22 388 137 48 362 330 458 330), lower := (rows 113 22 388 137 48 32 64 128 256), losses := [] }

theorem u1123 : Upper (D 2) (R 2) [112,20,384,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1123
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1124 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 388 137 272 106 106 234 362), lower := (rows 113 22 388 137 272 32 64 128 256), losses := [] }

theorem u1124 : Upper (D 2) (R 2) [112,20,384,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1124
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1125 : PairBound 9 := { available := 360, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 388 138 17 360 360 488 360), lower := (rows 113 22 388 138 17 32 64 128 256), losses := [] }

theorem u1125 : Upper (D 2) (R 2) [112,20,384,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1125
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1126 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 388 138 24 353 353 481 353), lower := (rows 113 22 388 138 24 32 64 128 256), losses := [] }

theorem u1126 : Upper (D 2) (R 2) [112,20,384,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1126
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1127 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 22 388 138 48 361 329 457 329), lower := (rows 113 22 388 138 48 32 64 128 256), losses := [] }

theorem u1127 : Upper (D 2) (R 2) [112,20,384,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1127
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1128 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 388 138 272 105 105 233 361), lower := (rows 113 22 388 138 272 32 64 128 256), losses := [] }

theorem u1128 : Upper (D 2) (R 2) [112,20,384,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1128
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1129 : PairBound 9 := { available := 330, camps := [{ cop := 1, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 113 22 388 168 17 362 330 458 330), lower := (rows 113 22 388 168 17 32 64 128 256), losses := [] }

theorem u1129 : Upper (D 2) (R 2) [112,20,384,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1129
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1130 : PairBound 9 := { available := 329, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 388 168 18 361 329 457 329), lower := (rows 113 22 388 168 18 32 64 128 256), losses := [] }

theorem u1130 : Upper (D 2) (R 2) [112,20,384,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1130
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1131 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 390, targets := 32 }], pairs := [(1,5)], upper := (rows 113 22 388 168 24 355 323 451 323), lower := (rows 113 22 388 168 24 32 64 128 256), losses := [] }

theorem u1131 : Upper (D 2) (R 2) [112,20,384,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1131
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1132 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 113 22 388 168 80 299 331 395 267), lower := (rows 113 22 388 168 80 32 64 128 256), losses := [] }

theorem u1132 : Upper (D 2) (R 2) [112,20,384,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1132
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1133 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 18, targets := 96 }], pairs := [(1,5),(1,6)], upper := (rows 113 22 388 168 272 107 75 203 331), lower := (rows 113 22 388 168 272 32 64 128 256), losses := [] }

theorem u1133 : Upper (D 2) (R 2) [112,20,384,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1133
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1134 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 131 140 266 20 368 368 496 368), lower := (rows 113 131 140 266 20 32 64 128 256), losses := [] }

theorem u1134 : Upper (D 2) (R 2) [112,129,136,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1134
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1135 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 131 140 266 48 372 340 468 340), lower := (rows 113 131 140 266 48 32 64 128 256), losses := [] }

theorem u1135 : Upper (D 2) (R 2) [112,129,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1135
    (constants 2).1 (constants 2).2 (by decide +kernel)

theorem m1136_4 : Upper (D 2) (R 2) [112,129,136,258,256,4] 13 :=
  permutation_upper _ _ _ [112,129,136,258,4,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u482

theorem m1136_16 : Upper (D 2) (R 2) [112,129,136,258,256,16] 13 :=
  permutation_upper _ _ _ [112,129,136,258,32,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u483

theorem m1136_64 : Upper (D 2) (R 2) [112,129,136,258,256,64] 13 :=
  permutation_upper _ _ _ [112,129,136,258,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u484

def r1136 : Route 9 := (fun mask => (mask,id))

def c1136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1136 : Upper (D 2) (R 2) [112,129,136,258,256] 13 := by
  apply FastRouting.sound _ _ [112,129,136,258,256] 13 (by decide) (choices 1) [4,16,64] r1136 c1136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1136_4
  · exact m1136_16
  · exact m1136_64

def b1137 : PairBound 9 := { available := 368, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 113 131 140 268 18 368 368 496 368), lower := (rows 113 131 140 268 18 32 64 128 256), losses := [] }

theorem u1137 : Upper (D 2) (R 2) [112,129,136,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1137
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1138 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 113 131 140 268 48 370 338 466 338), lower := (rows 113 131 140 268 48 32 64 128 256), losses := [] }

theorem u1138 : Upper (D 2) (R 2) [112,129,136,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1138
    (constants 2).1 (constants 2).2 (by decide +kernel)

def b1139 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 113 131 140 268 272 114 114 242 370), lower := (rows 113 131 140 268 272 32 64 128 256), losses := [] }

theorem u1139 : Upper (D 2) (R 2) [112,129,136,260,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 2) 14 b1139
    (constants 2).1 (constants 2).2 (by decide +kernel)

#print axioms u1139
end Delivery.IrregularNine14.P02
