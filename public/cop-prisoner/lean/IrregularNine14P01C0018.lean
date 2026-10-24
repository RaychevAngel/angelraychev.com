import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0002

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1080 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 22 292 138 144 40 67 195 323), lower := (rows 113 22 292 138 144 40 64 128 256), losses := [] }

theorem u1080 : Upper (D 1) (R 1) [112,20,288,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1080
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1081 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 22 292 138 144 96 75 139 267), lower := (rows 113 22 292 138 144 96 64 128 256), losses := [] }

theorem u1081 : Upper (D 1) (R 1) [112,20,288,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1081
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1082 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 113 22 292 200 144 33 74 138 266), lower := (rows 113 22 292 200 144 33 64 128 256), losses := [] }

theorem u1082 : Upper (D 1) (R 1) [112,20,288,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1082
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1083 : Route 9 := (fun mask => (mask,id))

def c1083 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1083 : Upper (D 1) (R 1) [112,20,288,192,128,2] 13 := by
  apply FastRouting.sound _ _ [112,20,288,192,128,2] 13 (by decide) (choices 1) [1,2,8] r1083 c1083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u134
  · exact u135
  · exact u136

def b1084 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 113 22 292 200 144 40 67 131 259), lower := (rows 113 22 292 200 144 40 64 128 256), losses := [] }

theorem u1084 : Upper (D 1) (R 1) [112,20,288,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1084
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1085 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 131 14 268 18 160 112 240 368), lower := (rows 113 131 14 268 18 160 64 128 256), losses := [] }

theorem u1085 : Upper (D 1) (R 1) [112,129,10,260,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1085
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1086 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 130, targets := 32 }], pairs := [(1,5)], upper := (rows 113 131 14 268 48 160 82 210 338), lower := (rows 113 131 14 268 48 160 64 128 256), losses := [] }

theorem u1086 : Upper (D 1) (R 1) [112,129,10,260,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1086
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1087 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 130, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 14 268 80 160 114 178 306), lower := (rows 113 131 14 268 80 160 64 128 256), losses := [] }

theorem u1087 : Upper (D 1) (R 1) [112,129,10,260,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1087
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1088 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 113 131 14 280 18 36 224 224 480), lower := (rows 113 131 14 280 18 36 64 128 256), losses := [] }

theorem u1088 : Upper (D 1) (R 1) [112,129,10,272,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1088
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1089 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 14 280 18 96 228 164 420), lower := (rows 113 131 14 280 18 96 64 128 256), losses := [] }

theorem u1089 : Upper (D 1) (R 1) [112,129,10,272,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1089
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1090 : PairBound 9 := { available := 100, camps := [], pairs := [(2,7)], upper := (rows 113 131 14 280 18 160 100 228 356), lower := (rows 113 131 14 280 18 160 64 128 256), losses := [{ target := 7, region := (rows 1 2 22 11 22 32 65 0 257), good := (rows 381 351 30 284 30 32 64 0 256) }] }

theorem u1090 : Upper (D 1) (R 1) [112,129,10,272,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1090
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1091 : PairBound 9 := { available := 100, camps := [], pairs := [(2,7)], upper := (rows 113 131 14 280 144 34 100 228 356), lower := (rows 113 131 14 280 144 34 64 128 256), losses := [{ target := 7, region := (rows 1 2 6 9 16 38 102 0 294), good := (rows 377 367 366 280 16 358 64 0 256) }] }

theorem u1091 : Upper (D 1) (R 1) [112,129,10,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1091
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1092 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 131 14 280 144 36 98 226 354), lower := (rows 113 131 14 280 144 36 64 128 256), losses := [] }

theorem u1092 : Upper (D 1) (R 1) [112,129,10,272,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1092
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1093 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 14 280 144 96 102 166 294), lower := (rows 113 131 14 280 144 96 64 128 256), losses := [] }

theorem u1093 : Upper (D 1) (R 1) [112,129,10,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1093
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1094 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 113 131 28 168 18 34 324 452 324), lower := (rows 113 131 28 168 18 34 64 128 256), losses := [] }

theorem u1094 : Upper (D 1) (R 1) [112,129,24,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1094
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1095 : PairBound 9 := { available := 322, camps := [], pairs := [], upper := (rows 113 131 28 168 18 36 322 450 322), lower := (rows 113 131 28 168 18 36 64 128 256), losses := [] }

theorem u1095 : Upper (D 1) (R 1) [112,129,24,160,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1095
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1096 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 28 168 18 96 326 390 262), lower := (rows 113 131 28 168 18 96 64 128 256), losses := [] }

theorem u1096 : Upper (D 1) (R 1) [112,129,24,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1096
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1097 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 131 28 168 18 288 70 198 326), lower := (rows 113 131 28 168 18 288 64 128 256), losses := [] }

theorem u1097 : Upper (D 1) (R 1) [112,129,24,160,2,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1097
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1098 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 113 131 28 296 18 34 196 196 452), lower := (rows 113 131 28 296 18 34 64 128 256), losses := [] }

theorem u1098 : Upper (D 1) (R 1) [112,129,24,288,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1098
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1099 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 131 28 296 18 36 194 194 450), lower := (rows 113 131 28 296 18 36 64 128 256), losses := [] }

theorem u1099 : Upper (D 1) (R 1) [112,129,24,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1099
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1100 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 28 296 18 96 198 134 390), lower := (rows 113 131 28 296 18 96 64 128 256), losses := [] }

theorem u1100 : Upper (D 1) (R 1) [112,129,24,288,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1100
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1101 : PairBound 9 := { available := 70, camps := [], pairs := [(2,7)], upper := (rows 113 131 28 296 18 160 70 198 326), lower := (rows 113 131 28 296 18 160 64 128 256), losses := [{ target := 7, region := (rows 1 2 7 9 18 32 82 0 274), good := (rows 381 351 348 296 342 32 64 0 256) }] }

theorem u1101 : Upper (D 1) (R 1) [112,129,24,288,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1101
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1102 : PairBound 9 := { available := 70, camps := [], pairs := [(2,7)], upper := (rows 113 131 28 296 144 34 70 198 326), lower := (rows 113 131 28 296 144 34 64 128 256), losses := [{ target := 7, region := (rows 1 2 5 42 16 34 66 0 258), good := (rows 125 367 28 296 16 362 64 0 256) }] }

theorem u1102 : Upper (D 1) (R 1) [112,129,24,288,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1102
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1103 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 113 131 28 296 144 36 66 194 322), lower := (rows 113 131 28 296 144 36 64 128 256), losses := [] }

theorem u1103 : Upper (D 1) (R 1) [112,129,24,288,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1103
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1104 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 28 296 144 96 70 134 262), lower := (rows 113 131 28 296 144 96 64 128 256), losses := [] }

theorem u1104 : Upper (D 1) (R 1) [112,129,24,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1104
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1105 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 113 131 28 392 18 34 100 228 356), lower := (rows 113 131 28 392 18 34 64 128 256), losses := [] }

theorem u1105 : Upper (D 1) (R 1) [112,129,24,384,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1105
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1106 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 131 28 392 18 36 98 226 354), lower := (rows 113 131 28 392 18 36 64 128 256), losses := [] }

theorem u1106 : Upper (D 1) (R 1) [112,129,24,384,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1106
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1107 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 28 392 18 96 102 166 294), lower := (rows 113 131 28 392 18 96 64 128 256), losses := [] }

theorem u1107 : Upper (D 1) (R 1) [112,129,24,384,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1107
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1108 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 113 131 140 280 18 34 100 228 356), lower := (rows 113 131 140 280 18 34 64 128 256), losses := [] }

theorem u1108 : Upper (D 1) (R 1) [112,129,136,272,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1108
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1109 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 131 140 280 18 36 98 226 354), lower := (rows 113 131 140 280 18 36 64 128 256), losses := [] }

theorem u1109 : Upper (D 1) (R 1) [112,129,136,272,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1109
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1110 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 131 140 280 18 96 102 166 294), lower := (rows 113 131 140 280 18 96 64 128 256), losses := [] }

theorem u1110 : Upper (D 1) (R 1) [112,129,136,272,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1110
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1111 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 473, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 7 280 144 34 104 232 360), lower := (rows 113 134 7 280 144 34 64 128 256), losses := [] }

theorem u1111 : Upper (D 1) (R 1) [112,132,3,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1111
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1112 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 134 7 280 144 40 98 226 354), lower := (rows 113 134 7 280 144 40 64 128 256), losses := [] }

theorem u1112 : Upper (D 1) (R 1) [112,132,3,272,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1112
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1113 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 7 280 144 96 106 170 298), lower := (rows 113 134 7 280 144 96 64 128 256), losses := [] }

theorem u1113 : Upper (D 1) (R 1) [112,132,3,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1113
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1114 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 13 266 18 160 112 240 368), lower := (rows 113 134 13 266 18 160 64 128 256), losses := [] }

theorem u1114 : Upper (D 1) (R 1) [112,132,9,258,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1114
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1115 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 13 266 48 160 82 210 338), lower := (rows 113 134 13 266 48 160 64 128 256), losses := [] }

theorem u1115 : Upper (D 1) (R 1) [112,132,9,258,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1115
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1116 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 13 266 80 160 114 178 306), lower := (rows 113 134 13 266 80 160 64 128 256), losses := [] }

theorem u1116 : Upper (D 1) (R 1) [112,132,9,258,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1116
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1117 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 14 265 18 160 112 240 368), lower := (rows 113 134 14 265 18 160 64 128 256), losses := [] }

theorem u1117 : Upper (D 1) (R 1) [112,132,10,257,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1117
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1118 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 14 265 48 160 82 210 338), lower := (rows 113 134 14 265 48 160 64 128 256), losses := [] }

theorem u1118 : Upper (D 1) (R 1) [112,132,10,257,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1118
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1119 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 14 265 80 160 114 178 306), lower := (rows 113 134 14 265 80 160 64 128 256), losses := [] }

theorem u1119 : Upper (D 1) (R 1) [112,132,10,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1119
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1120 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 134 14 280 144 33 98 226 354), lower := (rows 113 134 14 280 144 33 64 128 256), losses := [] }

theorem u1120 : Upper (D 1) (R 1) [112,132,10,272,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1120
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1121 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 14 280 144 34 97 225 353), lower := (rows 113 134 14 280 144 34 64 128 256), losses := [] }

theorem u1121 : Upper (D 1) (R 1) [112,132,10,272,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1121
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1122 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 14 280 144 96 99 163 291), lower := (rows 113 134 14 280 144 96 64 128 256), losses := [] }

theorem u1122 : Upper (D 1) (R 1) [112,132,10,272,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1122
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1123 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 113 134 28 296 18 33 194 194 450), lower := (rows 113 134 28 296 18 33 64 128 256), losses := [] }

theorem u1123 : Upper (D 1) (R 1) [112,132,24,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1123
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1124 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 113 134 28 296 18 34 193 193 449), lower := (rows 113 134 28 296 18 34 64 128 256), losses := [] }

theorem u1124 : Upper (D 1) (R 1) [112,132,24,288,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1124
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1125 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 28 296 18 96 195 131 387), lower := (rows 113 134 28 296 18 96 64 128 256), losses := [] }

theorem u1125 : Upper (D 1) (R 1) [112,132,24,288,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1125
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1126 : Route 9 := (fun mask => (mask,id))

def c1126 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1126 : Upper (D 1) (R 1) [112,132,24,288,2,128] 13 := by
  apply FastRouting.sound _ _ [112,132,24,288,2,128] 13 (by decide) (choices 1) [1,2] r1126 c1126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u137
  · exact u138

def b1127 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 113 134 28 296 144 33 66 194 322), lower := (rows 113 134 28 296 144 33 64 128 256), losses := [] }

theorem u1127 : Upper (D 1) (R 1) [112,132,24,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1127
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1128 : Route 9 := (fun mask => (mask,id))

def c1128 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1128 : Upper (D 1) (R 1) [112,132,24,288,128,2] 13 := by
  apply FastRouting.sound _ _ [112,132,24,288,128,2] 13 (by decide) (choices 1) [1,2] r1128 c1128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u139
  · exact u140

def b1129 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 28 296 144 96 67 131 259), lower := (rows 113 134 28 296 144 96 64 128 256), losses := [] }

theorem u1129 : Upper (D 1) (R 1) [112,132,24,288,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1129
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1130 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 134 268 11 18 160 112 240 368), lower := (rows 113 134 268 11 18 160 64 128 256), losses := [] }

theorem u1130 : Upper (D 1) (R 1) [112,132,264,3,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1130
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1131 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 268 11 48 160 82 210 338), lower := (rows 113 134 268 11 48 160 64 128 256), losses := [] }

theorem u1131 : Upper (D 1) (R 1) [112,132,264,3,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1131
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1132 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 268 11 80 160 114 178 306), lower := (rows 113 134 268 11 80 160 64 128 256), losses := [] }

theorem u1132 : Upper (D 1) (R 1) [112,132,264,3,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1132
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1133 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 113 134 276 11 18 40 224 224 480), lower := (rows 113 134 276 11 18 40 64 128 256), losses := [] }

theorem u1133 : Upper (D 1) (R 1) [112,132,272,3,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1133
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1134 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 276 11 18 96 232 168 424), lower := (rows 113 134 276 11 18 96 64 128 256), losses := [] }

theorem u1134 : Upper (D 1) (R 1) [112,132,272,3,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1134
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m1135_8 : Upper (D 1) (R 1) [112,132,272,3,2,128,8] 13 :=
  permutation_upper _ _ _ [112,132,272,3,2,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u141

theorem m1135_32 : Upper (D 1) (R 1) [112,132,272,3,2,128,32] 13 :=
  permutation_upper _ _ _ [112,132,272,3,2,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u142

def r1135 : Route 9 := (fun mask => (mask,id))

def c1135 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1135 : Upper (D 1) (R 1) [112,132,272,3,2,128] 13 := by
  apply FastRouting.sound _ _ [112,132,272,3,2,128] 13 (by decide) (choices 1) [8,32] r1135 c1135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m1135_8
  · exact m1135_32

def r1136 : Route 9 := (fun mask => (mask,id))

def c1136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1136 : Upper (D 1) (R 1) [112,132,272,3,128,2] 13 := by
  apply FastRouting.sound _ _ [112,132,272,3,128,2] 13 (by decide) (choices 1) [8,32] r1136 c1136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u143
  · exact u144

def b1137 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 134 276 11 144 40 98 226 354), lower := (rows 113 134 276 11 144 40 64 128 256), losses := [] }

theorem u1137 : Upper (D 1) (R 1) [112,132,272,3,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1137
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1138 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 276 11 144 96 106 170 298), lower := (rows 113 134 276 11 144 96 64 128 256), losses := [] }

theorem u1138 : Upper (D 1) (R 1) [112,132,272,3,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1138
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1139 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 113 134 276 42 18 33 200 200 456), lower := (rows 113 134 276 42 18 33 64 128 256), losses := [] }

theorem u1139 : Upper (D 1) (R 1) [112,132,272,34,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1139
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1139
end Delivery.IrregularNine14.P01
