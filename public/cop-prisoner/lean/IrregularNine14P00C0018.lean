import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0004

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1080 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 268 104 17 240 208 208 464), lower := (rows 23 35 268 104 17 32 64 128 256), losses := [] }

theorem u1080 : Upper (D 0) (R 0) [22,33,264,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1080
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1081 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 268 104 80 177 209 145 401), lower := (rows 23 35 268 104 80 32 64 128 256), losses := [] }

theorem u1081 : Upper (D 0) (R 0) [22,33,264,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1081
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1082 : Route 9 := (fun mask => (mask,id))

def c1082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1082 : Upper (D 0) (R 0) [22,33,264,96,128] 13 := by
  apply FastRouting.sound _ _ [22,33,264,96,128] 13 (by decide) (choices 1) [1,16,64,128] r1082 c1082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u250
  · exact u251
  · exact u252
  · exact u253

def b1083 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 268 200 17 240 240 240 496), lower := (rows 23 35 268 200 17 32 64 128 256), losses := [] }

theorem u1083 : Upper (D 0) (R 0) [22,33,264,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1083
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1084 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 268 200 48 241 209 209 465), lower := (rows 23 35 268 200 48 32 64 128 256), losses := [] }

theorem u1084 : Upper (D 0) (R 0) [22,33,264,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1084
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1085 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 268 200 80 177 241 177 433), lower := (rows 23 35 268 200 80 32 64 128 256), losses := [] }

theorem u1085 : Upper (D 0) (R 0) [22,33,264,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1085
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1086 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 324 56 17 232 200 200 456), lower := (rows 23 35 324 56 17 32 64 128 256), losses := [] }

theorem u1086 : Upper (D 0) (R 0) [22,33,320,48,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1086
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1087 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 23 35 324 56 24 225 193 193 449), lower := (rows 23 35 324 56 24 32 64 128 256), losses := [] }

theorem u1087 : Upper (D 0) (R 0) [22,33,320,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1087
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1088 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 56 80 169 201 137 393), lower := (rows 23 35 324 56 80 32 64 128 256), losses := [] }

theorem u1088 : Upper (D 0) (R 0) [22,33,320,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1088
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1089 : Route 9 := (fun mask => (mask,id))

def c1089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1089 : Upper (D 0) (R 0) [22,33,320,48,128] 13 := by
  apply FastRouting.sound _ _ [22,33,320,48,128] 13 (by decide) (choices 1) [1,8,64,128] r1089 c1089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u254
  · exact u255
  · exact u256
  · exact u257

def b1090 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 324 88 17 168 232 168 424), lower := (rows 23 35 324 88 17 32 64 128 256), losses := [] }

theorem u1090 : Upper (D 0) (R 0) [22,33,320,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1090
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1091 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 23 35 324 88 24 161 225 161 417), lower := (rows 23 35 324 88 24 32 64 128 256), losses := [] }

theorem u1091 : Upper (D 0) (R 0) [22,33,320,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1091
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1092 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 324 88 48 169 201 137 393), lower := (rows 23 35 324 88 48 32 64 128 256), losses := [] }

theorem u1092 : Upper (D 0) (R 0) [22,33,320,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1092
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1093 : Route 9 := (fun mask => (mask,id))

def c1093 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1093 : Upper (D 0) (R 0) [22,33,320,80,128] 13 := by
  apply FastRouting.sound _ _ [22,33,320,80,128] 13 (by decide) (choices 1) [1,8,128] r1093 c1093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u258
  · exact u259
  · exact u260

def b1094 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 324 104 17 184 216 152 408), lower := (rows 23 35 324 104 17 32 64 128 256), losses := [] }

theorem u1094 : Upper (D 0) (R 0) [22,33,320,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1094
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1095 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 23 35 324 104 24 177 209 145 401), lower := (rows 23 35 324 104 24 32 64 128 256), losses := [] }

theorem u1095 : Upper (D 0) (R 0) [22,33,320,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1095
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1096 : Route 9 := (fun mask => (mask,id))

def c1096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1096 : Upper (D 0) (R 0) [22,33,320,96,128] 13 := by
  apply FastRouting.sound _ _ [22,33,320,96,128] 13 (by decide) (choices 1) [1,8,16,128] r1096 c1096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u261
  · exact u262
  · exact u263
  · exact u264

def b1097 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 324 152 17 232 232 232 488), lower := (rows 23 35 324 152 17 32 64 128 256), losses := [] }

theorem u1097 : Upper (D 0) (R 0) [22,33,320,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1097
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1098 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 23 35 324 152 24 225 225 225 481), lower := (rows 23 35 324 152 24 32 64 128 256), losses := [] }

theorem u1098 : Upper (D 0) (R 0) [22,33,320,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1098
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1099 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 324 152 48 233 201 201 457), lower := (rows 23 35 324 152 48 32 64 128 256), losses := [] }

theorem u1099 : Upper (D 0) (R 0) [22,33,320,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1099
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1100 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 152 80 169 233 169 425), lower := (rows 23 35 324 152 80 32 64 128 256), losses := [] }

theorem u1100 : Upper (D 0) (R 0) [22,33,320,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1100
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1101 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 23 35 324 152 144 105 105 233 361), lower := (rows 23 35 324 152 144 32 64 128 256), losses := [] }

theorem u1101 : Upper (D 0) (R 0) [22,33,320,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1101
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1102 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 324 168 17 248 216 216 472), lower := (rows 23 35 324 168 17 32 64 128 256), losses := [] }

theorem u1102 : Upper (D 0) (R 0) [22,33,320,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1102
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1103 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 23 35 324 168 24 241 209 209 465), lower := (rows 23 35 324 168 24 32 64 128 256), losses := [] }

theorem u1103 : Upper (D 0) (R 0) [22,33,320,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1103
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1104 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 23 35 324 168 80 185 217 153 409), lower := (rows 23 35 324 168 80 32 64 128 256), losses := [] }

theorem u1104 : Upper (D 0) (R 0) [22,33,320,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1104
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1105 : Route 9 := (fun mask => (mask,id))

def c1105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1105 : Upper (D 0) (R 0) [22,33,320,160,128] 13 := by
  apply FastRouting.sound _ _ [22,33,320,160,128] 13 (by decide) (choices 1) [1,8,16,64] r1105 c1105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u265
  · exact u266
  · exact u267
  · exact u268

def b1106 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 492, targets := 1 }], pairs := [(2,0)], upper := (rows 23 35 324 200 17 184 248 184 440), lower := (rows 23 35 324 200 17 32 64 128 256), losses := [] }

theorem u1106 : Upper (D 0) (R 0) [22,33,320,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1106
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1107 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 23 35 324 200 24 177 241 177 433), lower := (rows 23 35 324 200 24 32 64 128 256), losses := [] }

theorem u1107 : Upper (D 0) (R 0) [22,33,320,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1107
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1108 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 35 324 200 48 185 217 153 409), lower := (rows 23 35 324 200 48 32 64 128 256), losses := [] }

theorem u1108 : Upper (D 0) (R 0) [22,33,320,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1108
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1109 : Route 9 := (fun mask => (mask,id))

def c1109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1109 : Upper (D 0) (R 0) [22,33,320,192,128] 13 := by
  apply FastRouting.sound _ _ [22,33,320,192,128] 13 (by decide) (choices 1) [1,8,16] r1109 c1109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u269
  · exact u270
  · exact u271

def b1110 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 23 42 196 265 17 240 240 240 496), lower := (rows 23 42 196 265 17 32 64 128 256), losses := [] }

theorem u1110 : Upper (D 0) (R 0) [22,40,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1110
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1111 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 23 42 196 265 48 241 209 209 465), lower := (rows 23 42 196 265 48 32 64 128 256), losses := [] }

theorem u1111 : Upper (D 0) (R 0) [22,40,192,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1111
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1112 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 23 42 196 265 80 177 241 177 433), lower := (rows 23 42 196 265 80 32 64 128 256), losses := [] }

theorem u1112 : Upper (D 0) (R 0) [22,40,192,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1112
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1113 : Route 9 := (fun mask => (mask,id))

def c1113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1113 : Upper (D 0) (R 0) [22,40,192,320,1] 13 := by
  apply FastRouting.sound _ _ [22,40,192,320,1] 13 (by decide) (choices 1) [1,16,128] r1113 c1113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u272
  · exact u273
  · exact u274

def b1114 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 23 42 196 328 48 177 209 145 401), lower := (rows 23 42 196 328 48 32 64 128 256), losses := [] }

theorem u1114 : Upper (D 0) (R 0) [22,40,192,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1114
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1115 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 362, targets := 128 }], pairs := [(1,7)], upper := (rows 23 42 196 328 144 49 113 177 305), lower := (rows 23 42 196 328 144 32 64 128 256), losses := [] }

theorem u1115 : Upper (D 0) (R 0) [22,40,192,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1115
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1116 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 234, targets := 1 }], pairs := [(1,0)], upper := (rows 23 42 261 200 17 240 240 240 496), lower := (rows 23 42 261 200 17 32 64 128 256), losses := [] }

theorem u1116 : Upper (D 0) (R 0) [22,40,257,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1116
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1117 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 23 42 261 200 48 241 209 209 465), lower := (rows 23 42 261 200 48 32 64 128 256), losses := [] }

theorem u1117 : Upper (D 0) (R 0) [22,40,257,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1117
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1118 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 23 42 261 200 80 177 241 177 433), lower := (rows 23 42 261 200 80 32 64 128 256), losses := [] }

theorem u1118 : Upper (D 0) (R 0) [22,40,257,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1118
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1119 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 23 42 324 137 17 240 240 240 496), lower := (rows 23 42 324 137 17 32 64 128 256), losses := [] }

theorem u1119 : Upper (D 0) (R 0) [22,40,320,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1119
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1120 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 23 42 324 137 48 241 209 209 465), lower := (rows 23 42 324 137 48 32 64 128 256), losses := [] }

theorem u1120 : Upper (D 0) (R 0) [22,40,320,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1120
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1121 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 23 42 324 137 80 177 241 177 433), lower := (rows 23 42 324 137 80 32 64 128 256), losses := [] }

theorem u1121 : Upper (D 0) (R 0) [22,40,320,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1121
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1122 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 356, targets := 128 }], pairs := [(2,7)], upper := (rows 23 42 324 137 144 113 113 241 369), lower := (rows 23 42 324 137 144 32 64 128 256), losses := [] }

theorem u1122 : Upper (D 0) (R 0) [22,40,320,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1122
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1123 : Route 9 := (fun mask => (mask,id))

def c1123 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1123 : Upper (D 0) (R 0) [22,40,320,192,1] 13 := by
  apply FastRouting.sound _ _ [22,40,320,192,1] 13 (by decide) (choices 1) [1,16,128] r1123 c1123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u275
  · exact u276
  · exact u277

def b1124 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 23 42 324 200 48 177 209 145 401), lower := (rows 23 42 324 200 48 32 64 128 256), losses := [] }

theorem u1124 : Upper (D 0) (R 0) [22,40,320,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1124
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1125 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 356, targets := 128 }], pairs := [(2,7)], upper := (rows 23 42 324 200 144 49 113 177 305), lower := (rows 23 42 324 200 144 32 64 128 256), losses := [] }

theorem u1125 : Upper (D 0) (R 0) [22,40,320,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1125
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1126 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 234, targets := 1 }], pairs := [(1,0)], upper := (rows 23 98 261 56 17 232 200 200 456), lower := (rows 23 98 261 56 17 32 64 128 256), losses := [] }

theorem u1126 : Upper (D 0) (R 0) [22,96,257,48,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1126
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1127 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 23 98 261 56 24 225 193 193 449), lower := (rows 23 98 261 56 24 32 64 128 256), losses := [] }

theorem u1127 : Upper (D 0) (R 0) [22,96,257,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1127
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1128 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 261 56 80 169 201 137 393), lower := (rows 23 98 261 56 80 32 64 128 256), losses := [] }

theorem u1128 : Upper (D 0) (R 0) [22,96,257,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1128
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1129 : Route 9 := (fun mask => (mask,id))

def c1129 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1129 : Upper (D 0) (R 0) [22,96,257,48,128] 13 := by
  apply FastRouting.sound _ _ [22,96,257,48,128] 13 (by decide) (choices 1) [1,8,64,128] r1129 c1129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u278
  · exact u279
  · exact u280
  · exact u281

def b1130 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 234, targets := 1 }], pairs := [(1,0)], upper := (rows 23 98 261 152 17 232 232 232 488), lower := (rows 23 98 261 152 17 32 64 128 256), losses := [] }

theorem u1130 : Upper (D 0) (R 0) [22,96,257,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1130
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1131 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 23 98 261 152 24 225 225 225 481), lower := (rows 23 98 261 152 24 32 64 128 256), losses := [] }

theorem u1131 : Upper (D 0) (R 0) [22,96,257,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1131
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1132 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 261 152 48 233 201 201 457), lower := (rows 23 98 261 152 48 32 64 128 256), losses := [] }

theorem u1132 : Upper (D 0) (R 0) [22,96,257,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1132
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1133 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 23 98 261 152 144 105 105 233 361), lower := (rows 23 98 261 152 144 32 64 128 256), losses := [] }

theorem u1133 : Upper (D 0) (R 0) [22,96,257,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1133
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1134 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 234, targets := 1 }], pairs := [(1,0)], upper := (rows 23 98 261 168 17 248 216 216 472), lower := (rows 23 98 261 168 17 32 64 128 256), losses := [] }

theorem u1134 : Upper (D 0) (R 0) [22,96,257,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1134
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1135 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 23 98 261 168 24 241 209 209 465), lower := (rows 23 98 261 168 24 32 64 128 256), losses := [] }

theorem u1135 : Upper (D 0) (R 0) [22,96,257,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1135
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1136 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 23 98 261 168 80 185 217 153 409), lower := (rows 23 98 261 168 80 32 64 128 256), losses := [] }

theorem u1136 : Upper (D 0) (R 0) [22,96,257,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1136
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1137 : Route 9 := (fun mask => (mask,id))

def c1137 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1137 : Upper (D 0) (R 0) [22,96,257,160,128] 13 := by
  apply FastRouting.sound _ _ [22,96,257,160,128] 13 (by decide) (choices 1) [1,8,16,64] r1137 c1137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u282
  · exact u283
  · exact u284
  · exact u285

def b1138 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 23 98 268 137 17 240 240 240 496), lower := (rows 23 98 268 137 17 32 64 128 256), losses := [] }

theorem u1138 : Upper (D 0) (R 0) [22,96,264,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1138
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1139 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 23 98 268 137 48 241 209 209 465), lower := (rows 23 98 268 137 48 32 64 128 256), losses := [] }

theorem u1139 : Upper (D 0) (R 0) [22,96,264,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1139
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1139
end Delivery.IrregularNine14.P00
