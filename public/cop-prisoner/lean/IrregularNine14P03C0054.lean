import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0018
import IrregularNine14P03C0019
import IrregularNine14P03C0020

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3240 : Route 9 := (fun mask => (mask,id))

def c3240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3240 : Upper (D 3) (R 3) [34,65,72,129,257] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,257] 13 (by decide) (choices 1) [4,16,128] r3240 c3240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1133
  · exact u1134
  · exact u1135

def r3241 : Route 9 := (fun mask => (mask,id))

def c3241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3241 : Upper (D 3) (R 3) [34,65,72,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,260] 13 (by decide) (choices 1) [1,16,128] r3241 c3241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1136
  · exact u1137
  · exact u1138

def r3242 : Route 9 := (fun mask => (mask,id))

def c3242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3242 : Upper (D 3) (R 3) [34,65,72,129,288] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,288] 13 (by decide) (choices 1) [1,4,16,128] r3242 c3242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1139
  · exact u1140
  · exact u1141
  · exact u1142

def r3243 : Route 9 := (fun mask => (mask,id))

def c3243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3243 : Upper (D 3) (R 3) [34,65,72,129,384] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,384] 13 (by decide) (choices 1) [1,4,16] r3243 c3243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1143
  · exact u1144
  · exact u1145

def b3244 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 140 145 305 369 433 305), lower := (rows 35 67 76 140 145 32 64 128 256), losses := [] }

theorem u3244 : Upper (D 3) (R 3) [34,65,72,132,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3244
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3245 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 140 176 305 337 401 273), lower := (rows 35 67 76 140 176 32 64 128 256), losses := [] }

theorem u3245 : Upper (D 3) (R 3) [34,65,72,132,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3245
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3246 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 140 273 177 241 177 433), lower := (rows 35 67 76 140 273 32 64 128 256), losses := [] }

theorem u3246 : Upper (D 3) (R 3) [34,65,72,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3246
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3247 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 140 304 177 209 145 401), lower := (rows 35 67 76 140 304 32 64 128 256), losses := [] }

theorem u3247 : Upper (D 3) (R 3) [34,65,72,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3247
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3248 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 140 400 49 113 177 305), lower := (rows 35 67 76 140 400 32 64 128 256), losses := [] }

theorem u3248 : Upper (D 3) (R 3) [34,65,72,132,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3248
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3249 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 152 145 293 357 421 293), lower := (rows 35 67 76 152 145 32 64 128 256), losses := [] }

theorem u3249 : Upper (D 3) (R 3) [34,65,72,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3249
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3250 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 152 148 289 353 417 289), lower := (rows 35 67 76 152 148 32 64 128 256), losses := [] }

theorem u3250 : Upper (D 3) (R 3) [34,65,72,144,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3250
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3251 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 152 176 293 325 389 261), lower := (rows 35 67 76 152 176 32 64 128 256), losses := [] }

theorem u3251 : Upper (D 3) (R 3) [34,65,72,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3251
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3252 : Route 9 := (fun mask => (mask,id))

def c3252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3252 : Upper (D 3) (R 3) [34,65,72,144,257] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,257] 13 (by decide) (choices 1) [1,4,128] r3252 c3252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1146
  · exact u1147
  · exact u1148

def b3253 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 152 276 161 225 161 417), lower := (rows 35 67 76 152 276 32 64 128 256), losses := [] }

theorem u3253 : Upper (D 3) (R 3) [34,65,72,144,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3253
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3254 : Route 9 := (fun mask => (mask,id))

def c3254 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3254 : Upper (D 3) (R 3) [34,65,72,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,72,144,288] 13 (by decide) (choices 1) [1,4,128] r3254 c3254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1149
  · exact u1150
  · exact u1151

def b3255 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 152 400 37 101 165 293), lower := (rows 35 67 76 152 400 32 64 128 256), losses := [] }

theorem u3255 : Upper (D 3) (R 3) [34,65,72,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3255
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3256 : Route 9 := (fun mask => (mask,id))

def c3256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u3256 : Upper (D 3) (R 3) [34,65,72,160,129] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,129] 13 (by decide) (choices 1) [1,4,16,256] r3256 c3256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1152
  · exact u1153
  · exact u1154
  · exact u1155

def b3257 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 168 148 305 337 401 273), lower := (rows 35 67 76 168 148 32 64 128 256), losses := [] }

theorem u3257 : Upper (D 3) (R 3) [34,65,72,160,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3257
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3258 : Route 9 := (fun mask => (mask,id))

def c3258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3258 : Upper (D 3) (R 3) [34,65,72,160,257] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,257] 13 (by decide) (choices 1) [1,4,16,128] r3258 c3258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1156
  · exact u1157
  · exact u1158
  · exact u1159

def r3259 : Route 9 := (fun mask => (mask,id))

def c3259 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3259 : Upper (D 3) (R 3) [34,65,72,160,260] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,260] 13 (by decide) (choices 1) [1,16,128] r3259 c3259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1160
  · exact u1161
  · exact u1162

def r3260 : Route 9 := (fun mask => (mask,id))

def c3260 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3260 : Upper (D 3) (R 3) [34,65,72,160,384] 13 := by
  apply FastRouting.sound _ _ [34,65,72,160,384] 13 (by decide) (choices 1) [1,4,16] r3260 c3260
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1163
  · exact u1164
  · exact u1165

def r3261 : Route 9 := (fun mask => (mask,id))

def c3261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3261 : Upper (D 3) (R 3) [34,65,72,257,129] 13 := by
  apply FastRouting.sound _ _ [34,65,72,257,129] 13 (by decide) (choices 1) [4,16,128] r3261 c3261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1166
  · exact u1167
  · exact u1168

def r3262 : Route 9 := (fun mask => (mask,id))

def c3262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3262 : Upper (D 3) (R 3) [34,65,72,257,132] 13 := by
  apply FastRouting.sound _ _ [34,65,72,257,132] 13 (by decide) (choices 1) [1,16,128] r3262 c3262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1169
  · exact u1170
  · exact u1171

def r3263 : Route 9 := (fun mask => (mask,id))

def c3263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3263 : Upper (D 3) (R 3) [34,65,72,257,160] 13 := by
  apply FastRouting.sound _ _ [34,65,72,257,160] 13 (by decide) (choices 1) [1,4,16,128] r3263 c3263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1172
  · exact u1173
  · exact u1174
  · exact u1175

def b3264 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 268 145 177 241 177 433), lower := (rows 35 67 76 268 145 32 64 128 256), losses := [] }

theorem u3264 : Upper (D 3) (R 3) [34,65,72,260,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3264
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3265 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 268 176 177 209 145 401), lower := (rows 35 67 76 268 176 32 64 128 256), losses := [] }

theorem u3265 : Upper (D 3) (R 3) [34,65,72,260,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3265
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3266 : Route 9 := (fun mask => (mask,id))

def c3266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3266 : Upper (D 3) (R 3) [34,65,72,272,129] 13 := by
  apply FastRouting.sound _ _ [34,65,72,272,129] 13 (by decide) (choices 1) [1,4,128] r3266 c3266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1176
  · exact u1177
  · exact u1178

def b3267 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 76 280 148 161 225 161 417), lower := (rows 35 67 76 280 148 32 64 128 256), losses := [] }

theorem u3267 : Upper (D 3) (R 3) [34,65,72,272,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3267
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3268 : Route 9 := (fun mask => (mask,id))

def c3268 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3268 : Upper (D 3) (R 3) [34,65,72,272,160] 13 := by
  apply FastRouting.sound _ _ [34,65,72,272,160] 13 (by decide) (choices 1) [1,4,128] r3268 c3268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1179
  · exact u1180
  · exact u1181

def r3269 : Route 9 := (fun mask => (mask,id))

def c3269 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3269 : Upper (D 3) (R 3) [34,65,72,288,129] 13 := by
  apply FastRouting.sound _ _ [34,65,72,288,129] 13 (by decide) (choices 1) [1,4,16,128] r3269 c3269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1182
  · exact u1183
  · exact u1184
  · exact u1185

def r3270 : Route 9 := (fun mask => (mask,id))

def c3270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3270 : Upper (D 3) (R 3) [34,65,72,288,132] 13 := by
  apply FastRouting.sound _ _ [34,65,72,288,132] 13 (by decide) (choices 1) [1,16,128] r3270 c3270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1186
  · exact u1187
  · exact u1188

def r3271 : Route 9 := (fun mask => (mask,id))

def c3271 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3271 : Upper (D 3) (R 3) [34,65,72,384,129] 13 := by
  apply FastRouting.sound _ _ [34,65,72,384,129] 13 (by decide) (choices 1) [1,4,16] r3271 c3271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1189
  · exact u1190
  · exact u1191

def b3272 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 392 148 49 113 177 305), lower := (rows 35 67 76 392 148 32 64 128 256), losses := [] }

theorem u3272 : Upper (D 3) (R 3) [34,65,72,384,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3272
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3273 : Route 9 := (fun mask => (mask,id))

def c3273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3273 : Upper (D 3) (R 3) [34,65,72,384,160] 13 := by
  apply FastRouting.sound _ _ [34,65,72,384,160] 13 (by decide) (choices 1) [1,4,16] r3273 c3273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1192
  · exact u1193
  · exact u1194

def b3274 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 137 148 313 345 409 281), lower := (rows 35 67 100 137 148 32 64 128 256), losses := [] }

theorem u3274 : Upper (D 3) (R 3) [34,65,96,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3274
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3275 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 137 273 188 220 156 412), lower := (rows 35 67 100 137 273 32 64 128 256), losses := [] }

theorem u3275 : Upper (D 3) (R 3) [34,65,96,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3275
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3276 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 137 276 185 217 153 409), lower := (rows 35 67 100 137 276 32 64 128 256), losses := [] }

theorem u3276 : Upper (D 3) (R 3) [34,65,96,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3276
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3277 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 137 280 181 213 149 405), lower := (rows 35 67 100 137 280 32 64 128 256), losses := [] }

theorem u3277 : Upper (D 3) (R 3) [34,65,96,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3277
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3278 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 137 400 61 93 157 285), lower := (rows 35 67 100 137 400 32 64 128 256), losses := [] }

theorem u3278 : Upper (D 3) (R 3) [34,65,96,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3278
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3279 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 140 273 185 217 153 409), lower := (rows 35 67 100 140 273 32 64 128 256), losses := [] }

theorem u3279 : Upper (D 3) (R 3) [34,65,96,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3279
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3280 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 140 280 177 209 145 401), lower := (rows 35 67 100 140 280 32 64 128 256), losses := [] }

theorem u3280 : Upper (D 3) (R 3) [34,65,96,132,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3280
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3281 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 140 400 57 89 153 281), lower := (rows 35 67 100 140 400 32 64 128 256), losses := [] }

theorem u3281 : Upper (D 3) (R 3) [34,65,96,132,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3281
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3282 : PairBound 9 := { available := 141, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 152 273 173 205 141 397), lower := (rows 35 67 100 152 273 32 64 128 256), losses := [] }

theorem u3282 : Upper (D 3) (R 3) [34,65,96,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3282
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3283 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 152 276 169 201 137 393), lower := (rows 35 67 100 152 276 32 64 128 256), losses := [] }

theorem u3283 : Upper (D 3) (R 3) [34,65,96,144,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3283
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3284 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 100 152 280 165 197 133 389), lower := (rows 35 67 100 152 280 32 64 128 256), losses := [] }

theorem u3284 : Upper (D 3) (R 3) [34,65,96,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3284
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3285 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 133 137 276 120 120 248 376), lower := (rows 35 67 133 137 276 32 64 128 256), losses := [] }

theorem u3285 : Upper (D 3) (R 3) [34,65,129,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3285
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3286 : PairBound 9 := { available := 92, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 133 137 304 124 92 220 348), lower := (rows 35 67 133 137 304 32 64 128 256), losses := [] }

theorem u3286 : Upper (D 3) (R 3) [34,65,129,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3286
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3287 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 133 137 336 60 124 188 316), lower := (rows 35 67 133 137 336 32 64 128 256), losses := [] }

theorem u3287 : Upper (D 3) (R 3) [34,65,129,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3287
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3288 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 140 273 120 120 248 376), lower := (rows 35 67 133 140 273 32 64 128 256), losses := [] }

theorem u3288 : Upper (D 3) (R 3) [34,65,129,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3288
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3289 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 140 280 113 113 241 369), lower := (rows 35 67 133 140 280 32 64 128 256), losses := [] }

theorem u3289 : Upper (D 3) (R 3) [34,65,129,132,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3289
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3290 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 140 304 121 89 217 345), lower := (rows 35 67 133 140 304 32 64 128 256), losses := [] }

theorem u3290 : Upper (D 3) (R 3) [34,65,129,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3290
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3291 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 133 140 336 57 121 185 313), lower := (rows 35 67 133 140 336 32 64 128 256), losses := [] }

theorem u3291 : Upper (D 3) (R 3) [34,65,129,132,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3291
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3292 : Route 9 := (fun mask => (mask,id))

def c3292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3292 : Upper (D 3) (R 3) [34,65,129,144,257] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,257] 13 (by decide) (choices 1) [4,8,64] r3292 c3292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1195
  · exact u1196
  · exact u1197

def b3293 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 133 152 276 105 105 233 361), lower := (rows 35 67 133 152 276 32 64 128 256), losses := [] }

theorem u3293 : Upper (D 3) (R 3) [34,65,129,144,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3293
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3294 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 133 152 280 101 101 229 357), lower := (rows 35 67 133 152 280 32 64 128 256), losses := [] }

theorem u3294 : Upper (D 3) (R 3) [34,65,129,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3294
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3295 : Route 9 := (fun mask => (mask,id))

def c3295 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3295 : Upper (D 3) (R 3) [34,65,129,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,288] 13 (by decide) (choices 1) [1,4,8,64] r3295 c3295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1198
  · exact u1199
  · exact u1200
  · exact u1201

def r3296 : Route 9 := (fun mask => (mask,id))

def c3296 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3296 : Upper (D 3) (R 3) [34,65,129,144,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,144,320] 13 (by decide) (choices 1) [1,4,8] r3296 c3296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1202
  · exact u1203
  · exact u1204

def r3297 : Route 9 := (fun mask => (mask,id))

def c3297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3297 : Upper (D 3) (R 3) [34,65,129,160,257] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,257] 13 (by decide) (choices 1) [4,8,16,64] r3297 c3297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1205
  · exact u1206
  · exact u1207
  · exact u1208

def r3298 : Route 9 := (fun mask => (mask,id))

def c3298 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3298 : Upper (D 3) (R 3) [34,65,129,160,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,260] 13 (by decide) (choices 1) [1,8,16,64] r3298 c3298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1209
  · exact u1210
  · exact u1211
  · exact u1212

def r3299 : Route 9 := (fun mask => (mask,id))

def c3299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3299 : Upper (D 3) (R 3) [34,65,129,160,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,160,264] 13 (by decide) (choices 1) [1,4,16,64] r3299 c3299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1213
  · exact u1214
  · exact u1215
  · exact u1216

#print axioms u3299
end Delivery.IrregularNine14.P03
