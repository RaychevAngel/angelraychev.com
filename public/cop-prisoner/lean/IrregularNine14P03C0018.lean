import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0002
import IrregularNine14P03C0003

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1080 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 200 273 33 212 148 404), lower := (rows 35 67 44 200 273 33 64 128 256), losses := [] }

theorem u1080 : Upper (D 3) (R 3) [34,65,40,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1080
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1081 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 44 200 273 36 209 145 401), lower := (rows 35 67 44 200 273 36 64 128 256), losses := [] }

theorem u1081 : Upper (D 3) (R 3) [34,65,40,192,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1081
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1082 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 44 200 273 48 197 133 389), lower := (rows 35 67 44 200 273 48 64 128 256), losses := [] }

theorem u1082 : Upper (D 3) (R 3) [34,65,40,192,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1082
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1083 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 200 273 160 85 149 277), lower := (rows 35 67 44 200 273 160 64 128 256), losses := [] }

theorem u1083 : Upper (D 3) (R 3) [34,65,40,192,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1083
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1084 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 200 276 33 209 145 401), lower := (rows 35 67 44 200 276 33 64 128 256), losses := [] }

theorem u1084 : Upper (D 3) (R 3) [34,65,40,192,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1084
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1085 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 44 200 276 48 193 129 385), lower := (rows 35 67 44 200 276 48 64 128 256), losses := [] }

theorem u1085 : Upper (D 3) (R 3) [34,65,40,192,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1085
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1086 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 200 276 160 81 145 273), lower := (rows 35 67 44 200 276 160 64 128 256), losses := [] }

theorem u1086 : Upper (D 3) (R 3) [34,65,40,192,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1086
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1087 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 200 400 33 85 149 277), lower := (rows 35 67 44 200 400 33 64 128 256), losses := [] }

theorem u1087 : Upper (D 3) (R 3) [34,65,40,192,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1087
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1088 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 67 44 200 400 36 81 145 273), lower := (rows 35 67 44 200 400 36 64 128 256), losses := [] }

theorem u1088 : Upper (D 3) (R 3) [34,65,40,192,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1088
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1089 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 67 44 200 400 48 69 133 261), lower := (rows 35 67 44 200 400 48 64 128 256), losses := [] }

theorem u1089 : Upper (D 3) (R 3) [34,65,40,192,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1089
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1090 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 265 84 33 208 144 400), lower := (rows 35 67 44 265 84 33 64 128 256), losses := [] }

theorem u1090 : Upper (D 3) (R 3) [34,65,40,257,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1090
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1091 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 44 265 84 48 193 129 385), lower := (rows 35 67 44 265 84 48 64 128 256), losses := [] }

theorem u1091 : Upper (D 3) (R 3) [34,65,40,257,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1091
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1092 : Route 9 := (fun mask => (mask,id))

def c1092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1092 : Upper (D 3) (R 3) [34,65,40,257,68,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,68,128] 13 (by decide) (choices 1) [1,16,128] r1092 c1092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u176
  · exact u177
  · exact u178

def b1093 : PairBound 9 := { available := 208, camps := [], pairs := [], upper := (rows 35 67 44 265 145 36 208 208 464), lower := (rows 35 67 44 265 145 36 64 128 256), losses := [] }

theorem u1093 : Upper (D 3) (R 3) [34,65,40,257,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1093
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1094 : PairBound 9 := { available := 196, camps := [], pairs := [], upper := (rows 35 67 44 265 145 48 196 196 452), lower := (rows 35 67 44 265 145 48 64 128 256), losses := [] }

theorem u1094 : Upper (D 3) (R 3) [34,65,40,257,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1094
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1095 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 265 145 96 212 148 404), lower := (rows 35 67 44 265 145 96 64 128 256), losses := [] }

theorem u1095 : Upper (D 3) (R 3) [34,65,40,257,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1095
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1096 : Route 9 := (fun mask => (mask,id))

def c1096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1096 : Upper (D 3) (R 3) [34,65,40,257,129,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,129,128] 13 (by decide) (choices 1) [4,16] r1096 c1096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u179
  · exact u180

def b1097 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 265 148 33 208 208 464), lower := (rows 35 67 44 265 148 33 64 128 256), losses := [] }

theorem u1097 : Upper (D 3) (R 3) [34,65,40,257,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1097
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1098 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 44 265 148 48 193 193 449), lower := (rows 35 67 44 265 148 48 64 128 256), losses := [] }

theorem u1098 : Upper (D 3) (R 3) [34,65,40,257,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1098
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1099 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 265 148 96 209 145 401), lower := (rows 35 67 44 265 148 96 64 128 256), losses := [] }

theorem u1099 : Upper (D 3) (R 3) [34,65,40,257,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1099
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1100 : Route 9 := (fun mask => (mask,id))

def c1100 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1100 : Upper (D 3) (R 3) [34,65,40,257,132,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,132,128] 13 (by decide) (choices 1) [1,16] r1100 c1100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u181
  · exact u182

def b1101 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 265 208 33 212 148 404), lower := (rows 35 67 44 265 208 33 64 128 256), losses := [] }

theorem u1101 : Upper (D 3) (R 3) [34,65,40,257,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1101
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1102 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 44 265 208 36 209 145 401), lower := (rows 35 67 44 265 208 36 64 128 256), losses := [] }

theorem u1102 : Upper (D 3) (R 3) [34,65,40,257,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1102
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1103 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 44 265 208 48 197 133 389), lower := (rows 35 67 44 265 208 48 64 128 256), losses := [] }

theorem u1103 : Upper (D 3) (R 3) [34,65,40,257,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1103
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1104 : Route 9 := (fun mask => (mask,id))

def c1104 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1104 : Upper (D 3) (R 3) [34,65,40,257,192,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,192,128] 13 (by decide) (choices 1) [1,4,16] r1104 c1104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u183
  · exact u184
  · exact u185

def b1105 : PairBound 9 := { available := 196, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 280 145 33 196 196 452), lower := (rows 35 67 44 280 145 33 64 128 256), losses := [] }

theorem u1105 : Upper (D 3) (R 3) [34,65,40,272,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1105
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1106 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 44 280 145 36 193 193 449), lower := (rows 35 67 44 280 145 36 64 128 256), losses := [] }

theorem u1106 : Upper (D 3) (R 3) [34,65,40,272,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1106
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1107 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 280 145 96 197 133 389), lower := (rows 35 67 44 280 145 96 64 128 256), losses := [] }

theorem u1107 : Upper (D 3) (R 3) [34,65,40,272,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1107
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1108 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 280 145 160 69 197 325), lower := (rows 35 67 44 280 145 160 64 128 256), losses := [] }

theorem u1108 : Upper (D 3) (R 3) [34,65,40,272,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1108
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1109 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 280 208 33 197 133 389), lower := (rows 35 67 44 280 208 33 64 128 256), losses := [] }

theorem u1109 : Upper (D 3) (R 3) [34,65,40,272,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1109
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1110 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 44 280 208 36 193 129 385), lower := (rows 35 67 44 280 208 36 64 128 256), losses := [] }

theorem u1110 : Upper (D 3) (R 3) [34,65,40,272,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1110
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1111 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 280 208 160 69 133 261), lower := (rows 35 67 44 280 208 160 64 128 256), losses := [] }

theorem u1111 : Upper (D 3) (R 3) [34,65,40,272,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1111
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1112 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 328 145 33 212 148 404), lower := (rows 35 67 44 328 145 33 64 128 256), losses := [] }

theorem u1112 : Upper (D 3) (R 3) [34,65,40,320,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1112
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1113 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 44 328 145 36 209 145 401), lower := (rows 35 67 44 328 145 36 64 128 256), losses := [] }

theorem u1113 : Upper (D 3) (R 3) [34,65,40,320,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1113
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1114 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 44 328 145 48 197 133 389), lower := (rows 35 67 44 328 145 48 64 128 256), losses := [] }

theorem u1114 : Upper (D 3) (R 3) [34,65,40,320,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1114
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1115 : Route 9 := (fun mask => (mask,id))

def c1115 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1115 : Upper (D 3) (R 3) [34,65,40,320,129,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,129,128] 13 (by decide) (choices 1) [1,4,16] r1115 c1115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u186
  · exact u187
  · exact u188

def b1116 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 328 148 33 209 145 401), lower := (rows 35 67 44 328 148 33 64 128 256), losses := [] }

theorem u1116 : Upper (D 3) (R 3) [34,65,40,320,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1116
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1117 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 44 328 148 48 193 129 385), lower := (rows 35 67 44 328 148 48 64 128 256), losses := [] }

theorem u1117 : Upper (D 3) (R 3) [34,65,40,320,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1117
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1118 : Route 9 := (fun mask => (mask,id))

def c1118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1118 : Upper (D 3) (R 3) [34,65,40,320,132,128] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,132,128] 13 (by decide) (choices 1) [1,16] r1118 c1118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u189
  · exact u190

def b1119 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 392 84 33 209 145 401), lower := (rows 35 67 44 392 84 33 64 128 256), losses := [] }

theorem u1119 : Upper (D 3) (R 3) [34,65,40,384,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1119
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1120 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 44 392 84 48 193 129 385), lower := (rows 35 67 44 392 84 48 64 128 256), losses := [] }

theorem u1120 : Upper (D 3) (R 3) [34,65,40,384,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1120
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1121 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 83, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 392 84 160 81 145 273), lower := (rows 35 67 44 392 84 160 64 128 256), losses := [] }

theorem u1121 : Upper (D 3) (R 3) [34,65,40,384,68,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1121
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1122 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 392 145 33 84 212 340), lower := (rows 35 67 44 392 145 33 64 128 256), losses := [] }

theorem u1122 : Upper (D 3) (R 3) [34,65,40,384,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1122
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1123 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 67 44 392 145 36 81 209 337), lower := (rows 35 67 44 392 145 36 64 128 256), losses := [] }

theorem u1123 : Upper (D 3) (R 3) [34,65,40,384,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1123
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1124 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 35 67 44 392 145 48 69 197 325), lower := (rows 35 67 44 392 145 48 64 128 256), losses := [] }

theorem u1124 : Upper (D 3) (R 3) [34,65,40,384,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1124
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1125 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 392 145 96 85 149 277), lower := (rows 35 67 44 392 145 96 64 128 256), losses := [] }

theorem u1125 : Upper (D 3) (R 3) [34,65,40,384,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1125
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1126 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 44 392 208 33 85 149 277), lower := (rows 35 67 44 392 208 33 64 128 256), losses := [] }

theorem u1126 : Upper (D 3) (R 3) [34,65,40,384,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1126
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1127 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 67 44 392 208 36 81 145 273), lower := (rows 35 67 44 392 208 36 64 128 256), losses := [] }

theorem u1127 : Upper (D 3) (R 3) [34,65,40,384,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1127
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1128 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 67 44 392 208 48 69 133 261), lower := (rows 35 67 44 392 208 48 64 128 256), losses := [] }

theorem u1128 : Upper (D 3) (R 3) [34,65,40,384,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1128
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1129 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 137 176 33 340 404 276), lower := (rows 35 67 76 137 176 33 64 128 256), losses := [] }

theorem u1129 : Upper (D 3) (R 3) [34,65,72,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1129
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1130 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 35 67 76 137 176 36 337 401 273), lower := (rows 35 67 76 137 176 36 64 128 256), losses := [] }

theorem u1130 : Upper (D 3) (R 3) [34,65,72,129,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1130
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1131 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 35 67 76 137 176 48 325 389 261), lower := (rows 35 67 76 137 176 48 64 128 256), losses := [] }

theorem u1131 : Upper (D 3) (R 3) [34,65,72,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1131
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1132 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 35 67 76 137 176 288 85 149 277), lower := (rows 35 67 76 137 176 288 64 128 256), losses := [] }

theorem u1132 : Upper (D 3) (R 3) [34,65,72,129,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1132
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1133 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 35 67 76 137 273 36 240 176 432), lower := (rows 35 67 76 137 273 36 64 128 256), losses := [] }

theorem u1133 : Upper (D 3) (R 3) [34,65,72,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1133
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1134 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 35 67 76 137 273 48 228 164 420), lower := (rows 35 67 76 137 273 48 64 128 256), losses := [] }

theorem u1134 : Upper (D 3) (R 3) [34,65,72,129,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1134
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1135 : Route 9 := (fun mask => (mask,id))

def c1135 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1135 : Upper (D 3) (R 3) [34,65,72,129,257,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,257,128] 13 (by decide) (choices 1) [4,16,32] r1135 c1135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u191
  · exact u192
  · exact u193

def b1136 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 137 276 33 240 176 432), lower := (rows 35 67 76 137 276 33 64 128 256), losses := [] }

theorem u1136 : Upper (D 3) (R 3) [34,65,72,129,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1136
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1137 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 76 137 276 48 225 161 417), lower := (rows 35 67 76 137 276 48 64 128 256), losses := [] }

theorem u1137 : Upper (D 3) (R 3) [34,65,72,129,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1137
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1138 : Route 9 := (fun mask => (mask,id))

def c1138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1138 : Upper (D 3) (R 3) [34,65,72,129,260,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,260,128] 13 (by decide) (choices 1) [1,16,32] r1138 c1138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u194
  · exact u195
  · exact u196

def b1139 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 137 304 33 212 148 404), lower := (rows 35 67 76 137 304 33 64 128 256), losses := [] }

theorem u1139 : Upper (D 3) (R 3) [34,65,72,129,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1139
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1139
end Delivery.IrregularNine14.P03
