import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0017
import IrregularNine14P03C0018

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3180 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 140 145 369 337 465 337), lower := (rows 35 67 44 140 145 32 64 128 256), losses := [] }

theorem u3180 : Upper (D 3) (R 3) [34,65,40,132,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3180
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3181 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 140 208 305 337 401 273), lower := (rows 35 67 44 140 208 32 64 128 256), losses := [] }

theorem u3181 : Upper (D 3) (R 3) [34,65,40,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3181
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3182 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 140 273 241 209 209 465), lower := (rows 35 67 44 140 273 32 64 128 256), losses := [] }

theorem u3182 : Upper (D 3) (R 3) [34,65,40,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3182
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3183 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 140 336 177 209 145 401), lower := (rows 35 67 44 140 336 32 64 128 256), losses := [] }

theorem u3183 : Upper (D 3) (R 3) [34,65,40,132,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3183
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3184 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 140 400 113 81 209 337), lower := (rows 35 67 44 140 400 32 64 128 256), losses := [] }

theorem u3184 : Upper (D 3) (R 3) [34,65,40,132,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3184
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3185 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 44 152 81 421 453 389 389), lower := (rows 35 67 44 152 81 32 64 128 256), losses := [] }

theorem u3185 : Upper (D 3) (R 3) [34,65,40,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3185
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3186 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 152 84 417 449 385 385), lower := (rows 35 67 44 152 84 32 64 128 256), losses := [] }

theorem u3186 : Upper (D 3) (R 3) [34,65,40,144,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3186
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3187 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 145 357 325 453 325), lower := (rows 35 67 44 152 145 32 64 128 256), losses := [] }

theorem u3187 : Upper (D 3) (R 3) [34,65,40,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3187
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3188 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 148 353 321 449 321), lower := (rows 35 67 44 152 148 32 64 128 256), losses := [] }

theorem u3188 : Upper (D 3) (R 3) [34,65,40,144,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3188
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3189 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 208 293 325 389 261), lower := (rows 35 67 44 152 208 32 64 128 256), losses := [] }

theorem u3189 : Upper (D 3) (R 3) [34,65,40,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3189
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3190 : Route 9 := (fun mask => (mask,id))

def c3190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3190 : Upper (D 3) (R 3) [34,65,40,144,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,257] 13 (by decide) (choices 1) [1,4,64,128] r3190 c3190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1069
  · exact u1070
  · exact u1071
  · exact u1072

def b3191 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 152 276 225 193 193 449), lower := (rows 35 67 44 152 276 32 64 128 256), losses := [] }

theorem u3191 : Upper (D 3) (R 3) [34,65,40,144,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3191
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3192 : Route 9 := (fun mask => (mask,id))

def c3192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3192 : Upper (D 3) (R 3) [34,65,40,144,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,320] 13 (by decide) (choices 1) [1,4,128] r3192 c3192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1073
  · exact u1074
  · exact u1075

def b3193 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 152 400 101 69 197 325), lower := (rows 35 67 44 152 400 32 64 128 256), losses := [] }

theorem u3193 : Upper (D 3) (R 3) [34,65,40,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3193
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3194 : Route 9 := (fun mask => (mask,id))

def c3194 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u3194 : Upper (D 3) (R 3) [34,65,40,192,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,129] 13 (by decide) (choices 1) [1,4,16,256] r3194 c3194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1076
  · exact u1077
  · exact u1078
  · exact u1079

def b3195 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 200 148 305 337 401 273), lower := (rows 35 67 44 200 148 32 64 128 256), losses := [] }

theorem u3195 : Upper (D 3) (R 3) [34,65,40,192,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3195
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3196 : Route 9 := (fun mask => (mask,id))

def c3196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3196 : Upper (D 3) (R 3) [34,65,40,192,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,257] 13 (by decide) (choices 1) [1,4,16,128] r3196 c3196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1080
  · exact u1081
  · exact u1082
  · exact u1083

def r3197 : Route 9 := (fun mask => (mask,id))

def c3197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3197 : Upper (D 3) (R 3) [34,65,40,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,260] 13 (by decide) (choices 1) [1,16,128] r3197 c3197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1084
  · exact u1085
  · exact u1086

def r3198 : Route 9 := (fun mask => (mask,id))

def c3198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3198 : Upper (D 3) (R 3) [34,65,40,192,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,384] 13 (by decide) (choices 1) [1,4,16] r3198 c3198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1087
  · exact u1088
  · exact u1089

def b3199 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 44 265 81 180 212 148 404), lower := (rows 35 67 44 265 81 32 64 128 256), losses := [] }

theorem u3199 : Upper (D 3) (R 3) [34,65,40,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3199
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3200 : Route 9 := (fun mask => (mask,id))

def c3200 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3200 : Upper (D 3) (R 3) [34,65,40,257,68] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,68] 13 (by decide) (choices 1) [1,16,128] r3200 c3200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1090
  · exact u1091
  · exact u1092

def r3201 : Route 9 := (fun mask => (mask,id))

def c3201 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3201 : Upper (D 3) (R 3) [34,65,40,257,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,129] 13 (by decide) (choices 1) [4,16,64,128] r3201 c3201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1093
  · exact u1094
  · exact u1095
  · exact u1096

def r3202 : Route 9 := (fun mask => (mask,id))

def c3202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3202 : Upper (D 3) (R 3) [34,65,40,257,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,132] 13 (by decide) (choices 1) [1,16,64,128] r3202 c3202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1097
  · exact u1098
  · exact u1099
  · exact u1100

def r3203 : Route 9 := (fun mask => (mask,id))

def c3203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3203 : Upper (D 3) (R 3) [34,65,40,257,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,257,192] 13 (by decide) (choices 1) [1,4,16,128] r3203 c3203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1101
  · exact u1102
  · exact u1103
  · exact u1104

def b3204 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 268 145 241 209 209 465), lower := (rows 35 67 44 268 145 32 64 128 256), losses := [] }

theorem u3204 : Upper (D 3) (R 3) [34,65,40,260,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3204
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3205 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 268 208 177 209 145 401), lower := (rows 35 67 44 268 208 32 64 128 256), losses := [] }

theorem u3205 : Upper (D 3) (R 3) [34,65,40,260,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3205
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3206 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 44 280 81 165 197 133 389), lower := (rows 35 67 44 280 81 32 64 128 256), losses := [] }

theorem u3206 : Upper (D 3) (R 3) [34,65,40,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3206
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3207 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 280 84 161 193 129 385), lower := (rows 35 67 44 280 84 32 64 128 256), losses := [] }

theorem u3207 : Upper (D 3) (R 3) [34,65,40,272,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3207
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3208 : Route 9 := (fun mask => (mask,id))

def c3208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3208 : Upper (D 3) (R 3) [34,65,40,272,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,272,129] 13 (by decide) (choices 1) [1,4,64,128] r3208 c3208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1105
  · exact u1106
  · exact u1107
  · exact u1108

def b3209 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 280 148 225 193 193 449), lower := (rows 35 67 44 280 148 32 64 128 256), losses := [] }

theorem u3209 : Upper (D 3) (R 3) [34,65,40,272,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3209
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3210 : Route 9 := (fun mask => (mask,id))

def c3210 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3210 : Upper (D 3) (R 3) [34,65,40,272,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,272,192] 13 (by decide) (choices 1) [1,4,128] r3210 c3210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1109
  · exact u1110
  · exact u1111

def r3211 : Route 9 := (fun mask => (mask,id))

def c3211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3211 : Upper (D 3) (R 3) [34,65,40,320,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,129] 13 (by decide) (choices 1) [1,4,16,128] r3211 c3211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1112
  · exact u1113
  · exact u1114
  · exact u1115

def r3212 : Route 9 := (fun mask => (mask,id))

def c3212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3212 : Upper (D 3) (R 3) [34,65,40,320,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,320,132] 13 (by decide) (choices 1) [1,16,128] r3212 c3212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1116
  · exact u1117
  · exact u1118

def b3213 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 44 392 81 181 213 149 405), lower := (rows 35 67 44 392 81 32 64 128 256), losses := [] }

theorem u3213 : Upper (D 3) (R 3) [34,65,40,384,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3213
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3214 : Route 9 := (fun mask => (mask,id))

def c3214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3214 : Upper (D 3) (R 3) [34,65,40,384,68] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,68] 13 (by decide) (choices 1) [1,16,128] r3214 c3214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1119
  · exact u1120
  · exact u1121

def r3215 : Route 9 := (fun mask => (mask,id))

def c3215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3215 : Upper (D 3) (R 3) [34,65,40,384,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,129] 13 (by decide) (choices 1) [1,4,16,64] r3215 c3215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1122
  · exact u1123
  · exact u1124
  · exact u1125

def b3216 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 392 148 113 81 209 337), lower := (rows 35 67 44 392 148 32 64 128 256), losses := [] }

theorem u3216 : Upper (D 3) (R 3) [34,65,40,384,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3216
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3217 : Route 9 := (fun mask => (mask,id))

def c3217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3217 : Upper (D 3) (R 3) [34,65,40,384,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,192] 13 (by decide) (choices 1) [1,4,16] r3217 c3217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1126
  · exact u1127
  · exact u1128

def b3218 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 137 148 312 376 440 312), lower := (rows 35 67 69 137 148 32 64 128 256), losses := [] }

theorem u3218 : Upper (D 3) (R 3) [34,65,65,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3218
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3219 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 137 176 316 348 412 284), lower := (rows 35 67 69 137 176 32 64 128 256), losses := [] }

theorem u3219 : Upper (D 3) (R 3) [34,65,65,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3219
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3220 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 137 276 184 248 184 440), lower := (rows 35 67 69 137 276 32 64 128 256), losses := [] }

theorem u3220 : Upper (D 3) (R 3) [34,65,65,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3220
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3221 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 137 280 180 244 180 436), lower := (rows 35 67 69 137 280 32 64 128 256), losses := [] }

theorem u3221 : Upper (D 3) (R 3) [34,65,65,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3221
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3222 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 137 304 188 220 156 412), lower := (rows 35 67 69 137 304 32 64 128 256), losses := [] }

theorem u3222 : Upper (D 3) (R 3) [34,65,65,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3222
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3223 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 137 400 60 124 188 316), lower := (rows 35 67 69 137 400 32 64 128 256), losses := [] }

theorem u3223 : Upper (D 3) (R 3) [34,65,65,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3223
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3224 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 140 176 313 345 409 281), lower := (rows 35 67 69 140 176 32 64 128 256), losses := [] }

theorem u3224 : Upper (D 3) (R 3) [34,65,65,132,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3224
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3225 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 140 273 184 248 184 440), lower := (rows 35 67 69 140 273 32 64 128 256), losses := [] }

theorem u3225 : Upper (D 3) (R 3) [34,65,65,132,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3225
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3226 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 140 280 177 241 177 433), lower := (rows 35 67 69 140 280 32 64 128 256), losses := [] }

theorem u3226 : Upper (D 3) (R 3) [34,65,65,132,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3226
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3227 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 140 304 185 217 153 409), lower := (rows 35 67 69 140 304 32 64 128 256), losses := [] }

theorem u3227 : Upper (D 3) (R 3) [34,65,65,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3227
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3228 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 140 400 57 121 185 313), lower := (rows 35 67 69 140 400 32 64 128 256), losses := [] }

theorem u3228 : Upper (D 3) (R 3) [34,65,65,132,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3228
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3229 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 152 273 172 236 172 428), lower := (rows 35 67 69 152 273 32 64 128 256), losses := [] }

theorem u3229 : Upper (D 3) (R 3) [34,65,65,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3229
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3230 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 152 276 169 233 169 425), lower := (rows 35 67 69 152 276 32 64 128 256), losses := [] }

theorem u3230 : Upper (D 3) (R 3) [34,65,65,144,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3230
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3231 : PairBound 9 := { available := 165, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 152 280 165 229 165 421), lower := (rows 35 67 69 152 280 32 64 128 256), losses := [] }

theorem u3231 : Upper (D 3) (R 3) [34,65,65,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3231
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3232 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 152 304 173 205 141 397), lower := (rows 35 67 69 152 304 32 64 128 256), losses := [] }

theorem u3232 : Upper (D 3) (R 3) [34,65,65,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3232
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3233 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 168 273 188 220 156 412), lower := (rows 35 67 69 168 273 32 64 128 256), losses := [] }

theorem u3233 : Upper (D 3) (R 3) [34,65,65,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3233
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3234 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 168 276 185 217 153 409), lower := (rows 35 67 69 168 276 32 64 128 256), losses := [] }

theorem u3234 : Upper (D 3) (R 3) [34,65,65,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3234
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3235 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 168 280 181 213 149 405), lower := (rows 35 67 69 168 280 32 64 128 256), losses := [] }

theorem u3235 : Upper (D 3) (R 3) [34,65,65,160,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3235
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3236 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 69 168 400 61 93 157 285), lower := (rows 35 67 69 168 400 32 64 128 256), losses := [] }

theorem u3236 : Upper (D 3) (R 3) [34,65,65,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3236
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3237 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 76 137 145 308 372 436 308), lower := (rows 35 67 76 137 145 32 64 128 256), losses := [] }

theorem u3237 : Upper (D 3) (R 3) [34,65,72,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3237
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3238 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 76 137 148 305 369 433 305), lower := (rows 35 67 76 137 148 32 64 128 256), losses := [] }

theorem u3238 : Upper (D 3) (R 3) [34,65,72,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3238
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3239 : Route 9 := (fun mask => (mask,id))

def c3239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u3239 : Upper (D 3) (R 3) [34,65,72,129,160] 13 := by
  apply FastRouting.sound _ _ [34,65,72,129,160] 13 (by decide) (choices 1) [1,4,16,256] r3239 c3239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1129
  · exact u1130
  · exact u1131
  · exact u1132

#print axioms u3239
end Delivery.IrregularNine14.P03
