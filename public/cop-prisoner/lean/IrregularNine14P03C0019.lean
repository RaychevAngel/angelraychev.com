import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0003

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1140 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 76 137 304 36 209 145 401), lower := (rows 35 67 76 137 304 36 64 128 256), losses := [] }

theorem u1140 : Upper (D 3) (R 3) [34,65,72,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1140
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1141 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 76 137 304 48 197 133 389), lower := (rows 35 67 76 137 304 48 64 128 256), losses := [] }

theorem u1141 : Upper (D 3) (R 3) [34,65,72,129,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1141
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1142 : Route 9 := (fun mask => (mask,id))

def c1142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1142 : Upper (D 3) (R 3) [34,65,72,129,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,288,128] 13 (by decide) (choices 1) [1,4,16] r1142 c1142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u197
  · exact u198
  · exact u199

def b1143 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 137 400 33 116 180 308), lower := (rows 35 67 76 137 400 33 64 128 256), losses := [] }

theorem u1143 : Upper (D 3) (R 3) [34,65,72,129,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1143
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1144 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 76 137 400 36 113 177 305), lower := (rows 35 67 76 137 400 36 64 128 256), losses := [] }

theorem u1144 : Upper (D 3) (R 3) [34,65,72,129,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1144
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1145 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 76 137 400 48 101 165 293), lower := (rows 35 67 76 137 400 48 64 128 256), losses := [] }

theorem u1145 : Upper (D 3) (R 3) [34,65,72,129,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1145
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1146 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 152 273 33 228 164 420), lower := (rows 35 67 76 152 273 33 64 128 256), losses := [] }

theorem u1146 : Upper (D 3) (R 3) [34,65,72,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1146
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1147 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 76 152 273 36 225 161 417), lower := (rows 35 67 76 152 273 36 64 128 256), losses := [] }

theorem u1147 : Upper (D 3) (R 3) [34,65,72,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1147
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1148 : Route 9 := (fun mask => (mask,id))

def c1148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1148 : Upper (D 3) (R 3) [34,65,72,144,257,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,257,128] 13 (by decide) (choices 1) [1,4,32] r1148 c1148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u200
  · exact u201
  · exact u202

def b1149 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 152 304 33 197 133 389), lower := (rows 35 67 76 152 304 33 64 128 256), losses := [] }

theorem u1149 : Upper (D 3) (R 3) [34,65,72,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1149
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1150 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 76 152 304 36 193 129 385), lower := (rows 35 67 76 152 304 36 64 128 256), losses := [] }

theorem u1150 : Upper (D 3) (R 3) [34,65,72,144,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1150
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1151 : Route 9 := (fun mask => (mask,id))

def c1151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1151 : Upper (D 3) (R 3) [34,65,72,144,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,288,128] 13 (by decide) (choices 1) [1,4] r1151 c1151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u203
  · exact u204

def b1152 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 168 145 33 340 404 276), lower := (rows 35 67 76 168 145 33 64 128 256), losses := [] }

theorem u1152 : Upper (D 3) (R 3) [34,65,72,160,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1152
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1153 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 35 67 76 168 145 36 337 401 273), lower := (rows 35 67 76 168 145 36 64 128 256), losses := [] }

theorem u1153 : Upper (D 3) (R 3) [34,65,72,160,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1153
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1154 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 35 67 76 168 145 48 325 389 261), lower := (rows 35 67 76 168 145 48 64 128 256), losses := [] }

theorem u1154 : Upper (D 3) (R 3) [34,65,72,160,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1154
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1155 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 35 67 76 168 145 288 85 149 277), lower := (rows 35 67 76 168 145 288 64 128 256), losses := [] }

theorem u1155 : Upper (D 3) (R 3) [34,65,72,160,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1155
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1156 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 168 273 33 212 148 404), lower := (rows 35 67 76 168 273 33 64 128 256), losses := [] }

theorem u1156 : Upper (D 3) (R 3) [34,65,72,160,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1156
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1157 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 76 168 273 36 209 145 401), lower := (rows 35 67 76 168 273 36 64 128 256), losses := [] }

theorem u1157 : Upper (D 3) (R 3) [34,65,72,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1157
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1158 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 76 168 273 48 197 133 389), lower := (rows 35 67 76 168 273 48 64 128 256), losses := [] }

theorem u1158 : Upper (D 3) (R 3) [34,65,72,160,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1158
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1159 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 168 273 160 85 149 277), lower := (rows 35 67 76 168 273 160 64 128 256), losses := [] }

theorem u1159 : Upper (D 3) (R 3) [34,65,72,160,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1159
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1160 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 168 276 33 209 145 401), lower := (rows 35 67 76 168 276 33 64 128 256), losses := [] }

theorem u1160 : Upper (D 3) (R 3) [34,65,72,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1160
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1161 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 76 168 276 48 193 129 385), lower := (rows 35 67 76 168 276 48 64 128 256), losses := [] }

theorem u1161 : Upper (D 3) (R 3) [34,65,72,160,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1161
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1162 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 168 276 160 81 145 273), lower := (rows 35 67 76 168 276 160 64 128 256), losses := [] }

theorem u1162 : Upper (D 3) (R 3) [34,65,72,160,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1162
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1163 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 168 400 33 85 149 277), lower := (rows 35 67 76 168 400 33 64 128 256), losses := [] }

theorem u1163 : Upper (D 3) (R 3) [34,65,72,160,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1163
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1164 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 67 76 168 400 36 81 145 273), lower := (rows 35 67 76 168 400 36 64 128 256), losses := [] }

theorem u1164 : Upper (D 3) (R 3) [34,65,72,160,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1164
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1165 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 67 76 168 400 48 69 133 261), lower := (rows 35 67 76 168 400 48 64 128 256), losses := [] }

theorem u1165 : Upper (D 3) (R 3) [34,65,72,160,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1165
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1166 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 35 67 76 265 145 36 240 176 432), lower := (rows 35 67 76 265 145 36 64 128 256), losses := [] }

theorem u1166 : Upper (D 3) (R 3) [34,65,72,257,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1166
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1167 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 35 67 76 265 145 48 228 164 420), lower := (rows 35 67 76 265 145 48 64 128 256), losses := [] }

theorem u1167 : Upper (D 3) (R 3) [34,65,72,257,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1167
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1168 : Route 9 := (fun mask => (mask,id))

def c1168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1168 : Upper (D 3) (R 3) [34,65,72,257,129,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,257,129,128] 13 (by decide) (choices 1) [4,16,32] r1168 c1168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u205
  · exact u206
  · exact u207

def b1169 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 265 148 33 240 176 432), lower := (rows 35 67 76 265 148 33 64 128 256), losses := [] }

theorem u1169 : Upper (D 3) (R 3) [34,65,72,257,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1169
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1170 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 76 265 148 48 225 161 417), lower := (rows 35 67 76 265 148 48 64 128 256), losses := [] }

theorem u1170 : Upper (D 3) (R 3) [34,65,72,257,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1170
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1171 : Route 9 := (fun mask => (mask,id))

def c1171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1171 : Upper (D 3) (R 3) [34,65,72,257,132,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,257,132,128] 13 (by decide) (choices 1) [1,16,32] r1171 c1171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u208
  · exact u209
  · exact u210

def b1172 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 265 176 33 212 148 404), lower := (rows 35 67 76 265 176 33 64 128 256), losses := [] }

theorem u1172 : Upper (D 3) (R 3) [34,65,72,257,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1172
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1173 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 76 265 176 36 209 145 401), lower := (rows 35 67 76 265 176 36 64 128 256), losses := [] }

theorem u1173 : Upper (D 3) (R 3) [34,65,72,257,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1173
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1174 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 76 265 176 48 197 133 389), lower := (rows 35 67 76 265 176 48 64 128 256), losses := [] }

theorem u1174 : Upper (D 3) (R 3) [34,65,72,257,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1174
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1175 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 265 176 160 85 149 277), lower := (rows 35 67 76 265 176 160 64 128 256), losses := [] }

theorem u1175 : Upper (D 3) (R 3) [34,65,72,257,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1175
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1176 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 280 145 33 228 164 420), lower := (rows 35 67 76 280 145 33 64 128 256), losses := [] }

theorem u1176 : Upper (D 3) (R 3) [34,65,72,272,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1176
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1177 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 76 280 145 36 225 161 417), lower := (rows 35 67 76 280 145 36 64 128 256), losses := [] }

theorem u1177 : Upper (D 3) (R 3) [34,65,72,272,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1177
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1178 : Route 9 := (fun mask => (mask,id))

def c1178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1178 : Upper (D 3) (R 3) [34,65,72,272,129,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,272,129,128] 13 (by decide) (choices 1) [1,4,32] r1178 c1178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u211
  · exact u212
  · exact u213

def b1179 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 280 176 33 197 133 389), lower := (rows 35 67 76 280 176 33 64 128 256), losses := [] }

theorem u1179 : Upper (D 3) (R 3) [34,65,72,272,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1179
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1180 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 76 280 176 36 193 129 385), lower := (rows 35 67 76 280 176 36 64 128 256), losses := [] }

theorem u1180 : Upper (D 3) (R 3) [34,65,72,272,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1180
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1181 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 280 176 160 69 133 261), lower := (rows 35 67 76 280 176 160 64 128 256), losses := [] }

theorem u1181 : Upper (D 3) (R 3) [34,65,72,272,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1181
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1182 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 296 145 33 212 148 404), lower := (rows 35 67 76 296 145 33 64 128 256), losses := [] }

theorem u1182 : Upper (D 3) (R 3) [34,65,72,288,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1182
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1183 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 67 76 296 145 36 209 145 401), lower := (rows 35 67 76 296 145 36 64 128 256), losses := [] }

theorem u1183 : Upper (D 3) (R 3) [34,65,72,288,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1183
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1184 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 67 76 296 145 48 197 133 389), lower := (rows 35 67 76 296 145 48 64 128 256), losses := [] }

theorem u1184 : Upper (D 3) (R 3) [34,65,72,288,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1184
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1185 : Route 9 := (fun mask => (mask,id))

def c1185 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1185 : Upper (D 3) (R 3) [34,65,72,288,129,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,288,129,128] 13 (by decide) (choices 1) [1,4,16] r1185 c1185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u214
  · exact u215
  · exact u216

def b1186 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 296 148 33 209 145 401), lower := (rows 35 67 76 296 148 33 64 128 256), losses := [] }

theorem u1186 : Upper (D 3) (R 3) [34,65,72,288,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1186
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1187 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 76 296 148 48 193 129 385), lower := (rows 35 67 76 296 148 48 64 128 256), losses := [] }

theorem u1187 : Upper (D 3) (R 3) [34,65,72,288,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1187
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1188 : Route 9 := (fun mask => (mask,id))

def c1188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1188 : Upper (D 3) (R 3) [34,65,72,288,132,128] 13 := by
  apply FastRouting.sound _ _ [34,65,72,288,132,128] 13 (by decide) (choices 1) [1,16] r1188 c1188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u217
  · exact u218

def b1189 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 392 145 33 116 180 308), lower := (rows 35 67 76 392 145 33 64 128 256), losses := [] }

theorem u1189 : Upper (D 3) (R 3) [34,65,72,384,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1189
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1190 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 76 392 145 36 113 177 305), lower := (rows 35 67 76 392 145 36 64 128 256), losses := [] }

theorem u1190 : Upper (D 3) (R 3) [34,65,72,384,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1190
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1191 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 76 392 145 48 101 165 293), lower := (rows 35 67 76 392 145 48 64 128 256), losses := [] }

theorem u1191 : Upper (D 3) (R 3) [34,65,72,384,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1191
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1192 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 392 176 33 85 149 277), lower := (rows 35 67 76 392 176 33 64 128 256), losses := [] }

theorem u1192 : Upper (D 3) (R 3) [34,65,72,384,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1192
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1193 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 67 76 392 176 36 81 145 273), lower := (rows 35 67 76 392 176 36 64 128 256), losses := [] }

theorem u1193 : Upper (D 3) (R 3) [34,65,72,384,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1193
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1194 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 67 76 392 176 48 69 133 261), lower := (rows 35 67 76 392 176 48 64 128 256), losses := [] }

theorem u1194 : Upper (D 3) (R 3) [34,65,72,384,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1194
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1195 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 35 67 133 152 273 36 104 232 360), lower := (rows 35 67 133 152 273 36 64 128 256), losses := [] }

theorem u1195 : Upper (D 3) (R 3) [34,65,129,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1195
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1196 : PairBound 9 := { available := 100, camps := [], pairs := [], upper := (rows 35 67 133 152 273 40 100 228 356), lower := (rows 35 67 133 152 273 40 64 128 256), losses := [] }

theorem u1196 : Upper (D 3) (R 3) [34,65,129,144,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1196
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1197 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 133 152 273 96 108 172 300), lower := (rows 35 67 133 152 273 96 64 128 256), losses := [] }

theorem u1197 : Upper (D 3) (R 3) [34,65,129,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1197
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1198 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 133 152 304 33 76 204 332), lower := (rows 35 67 133 152 304 33 64 128 256), losses := [] }

theorem u1198 : Upper (D 3) (R 3) [34,65,129,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1198
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1199 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 35 67 133 152 304 36 73 201 329), lower := (rows 35 67 133 152 304 36 64 128 256), losses := [] }

theorem u1199 : Upper (D 3) (R 3) [34,65,129,144,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1199
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1199
end Delivery.IrregularNine14.P03
