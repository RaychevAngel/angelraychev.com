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

def b1200 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 262 148 137 18 40 98 226 354), lower := (rows 113 262 148 137 18 40 64 128 256), losses := [] }

theorem u1200 : Upper (D 1) (R 1) [112,260,144,129,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1200
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1201 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 148 137 18 96 106 170 298), lower := (rows 113 262 148 137 18 96 64 128 256), losses := [] }

theorem u1201 : Upper (D 1) (R 1) [112,260,144,129,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1201
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1202 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 262 148 168 18 33 74 202 330), lower := (rows 113 262 148 168 18 33 64 128 256), losses := [] }

theorem u1202 : Upper (D 1) (R 1) [112,260,144,160,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1202
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1203 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 113 262 148 168 18 34 73 201 329), lower := (rows 113 262 148 168 18 34 64 128 256), losses := [] }

theorem u1203 : Upper (D 1) (R 1) [112,260,144,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1203
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1204 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 262 148 168 18 40 67 195 323), lower := (rows 113 262 148 168 18 40 64 128 256), losses := [] }

theorem u1204 : Upper (D 1) (R 1) [112,260,144,160,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1204
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1205 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 148 168 18 96 75 139 267), lower := (rows 113 262 148 168 18 96 64 128 256), losses := [] }

theorem u1205 : Upper (D 1) (R 1) [112,260,144,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1205
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1206 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 209, targets := 2 }], pairs := [(0,1)], upper := (rows 113 274 13 14 144 34 224 224 480), lower := (rows 113 274 13 14 144 34 64 128 256), losses := [] }

theorem u1206 : Upper (D 1) (R 1) [112,272,9,6,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1206
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1207 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 13 14 144 96 226 162 418), lower := (rows 113 274 13 14 144 96 64 128 256), losses := [] }

theorem u1207 : Upper (D 1) (R 1) [112,272,9,6,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1207
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1208 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 258, targets := 128 }], pairs := [(1,7)], upper := (rows 113 274 13 14 144 160 98 226 354), lower := (rows 113 274 13 14 144 160 64 128 256), losses := [] }

theorem u1208 : Upper (D 1) (R 1) [112,272,9,6,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1208
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1209 : Route 9 := (fun mask => (mask,id))

def c1209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1209 : Upper (D 1) (R 1) [112,272,9,130,128,2] 13 := by
  apply FastRouting.sound _ _ [112,272,9,130,128,2] 13 (by decide) (choices 1) [4,32] r1209 c1209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u149
  · exact u150

def b1210 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 274 13 138 144 36 98 226 354), lower := (rows 113 274 13 138 144 36 64 128 256), losses := [] }

theorem u1210 : Upper (D 1) (R 1) [112,272,9,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1210
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1211 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 13 138 144 96 102 166 294), lower := (rows 113 274 13 138 144 96 64 128 256), losses := [] }

theorem u1211 : Upper (D 1) (R 1) [112,272,9,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1211
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1212 : Route 9 := (fun mask => (mask,id))

def c1212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1212 : Upper (D 1) (R 1) [112,272,10,129,128,2] 13 := by
  apply FastRouting.sound _ _ [112,272,10,129,128,2] 13 (by decide) (choices 1) [4,32] r1212 c1212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u151
  · exact u152

def b1213 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 113 274 14 137 144 36 98 226 354), lower := (rows 113 274 14 137 144 36 64 128 256), losses := [] }

theorem u1213 : Upper (D 1) (R 1) [112,272,10,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1213
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1214 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 14 137 144 96 102 166 294), lower := (rows 113 274 14 137 144 96 64 128 256), losses := [] }

theorem u1214 : Upper (D 1) (R 1) [112,272,10,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1214
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1215 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 274 14 168 144 33 70 198 326), lower := (rows 113 274 14 168 144 33 64 128 256), losses := [] }

theorem u1215 : Upper (D 1) (R 1) [112,272,10,160,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1215
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1216 : Route 9 := (fun mask => (mask,id))

def c1216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1216 : Upper (D 1) (R 1) [112,272,10,160,128,2] 13 := by
  apply FastRouting.sound _ _ [112,272,10,160,128,2] 13 (by decide) (choices 1) [1,4] r1216 c1216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u153
  · exact u154

def b1217 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 274 14 168 144 36 67 195 323), lower := (rows 113 274 14 168 144 36 64 128 256), losses := [] }

theorem u1217 : Upper (D 1) (R 1) [112,272,10,160,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1217
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1218 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 14 168 144 96 71 135 263), lower := (rows 113 274 14 168 144 96 64 128 256), losses := [] }

theorem u1218 : Upper (D 1) (R 1) [112,272,10,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1218
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1219 : PairBound 9 := { available := 140, camps := [], pairs := [], upper := (rows 113 274 38 74 144 33 204 140 396), lower := (rows 113 274 38 74 144 33 64 128 256), losses := [] }

theorem u1219 : Upper (D 1) (R 1) [112,272,34,66,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1219
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1220 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 113 274 38 74 144 36 201 137 393), lower := (rows 113 274 38 74 144 36 64 128 256), losses := [] }

theorem u1220 : Upper (D 1) (R 1) [112,272,34,66,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1220
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1221 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 113 274 38 74 144 40 197 133 389), lower := (rows 113 274 38 74 144 40 64 128 256), losses := [] }

theorem u1221 : Upper (D 1) (R 1) [112,272,34,66,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1221
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1222 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 274 38 74 144 160 77 141 269), lower := (rows 113 274 38 74 144 160 64 128 256), losses := [] }

theorem u1222 : Upper (D 1) (R 1) [112,272,34,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1222
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1223 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 113 274 38 76 144 33 202 138 394), lower := (rows 113 274 38 76 144 33 64 128 256), losses := [] }

theorem u1223 : Upper (D 1) (R 1) [112,272,34,68,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1223
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1224 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 113 274 38 76 144 34 201 137 393), lower := (rows 113 274 38 76 144 34 64 128 256), losses := [] }

theorem u1224 : Upper (D 1) (R 1) [112,272,34,68,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1224
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1225 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 113 274 38 76 144 40 195 131 387), lower := (rows 113 274 38 76 144 40 64 128 256), losses := [] }

theorem u1225 : Upper (D 1) (R 1) [112,272,34,68,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1225
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1226 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 274 38 76 144 160 75 139 267), lower := (rows 113 274 38 76 144 160 64 128 256), losses := [] }

theorem u1226 : Upper (D 1) (R 1) [112,272,34,68,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1226
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1227 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 113 274 38 137 144 34 76 204 332), lower := (rows 113 274 38 137 144 34 64 128 256), losses := [] }

theorem u1227 : Upper (D 1) (R 1) [112,272,34,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1227
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1228 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 274 38 137 144 36 74 202 330), lower := (rows 113 274 38 137 144 36 64 128 256), losses := [] }

theorem u1228 : Upper (D 1) (R 1) [112,272,34,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1228
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1229 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 274 38 137 144 40 70 198 326), lower := (rows 113 274 38 137 144 40 64 128 256), losses := [] }

theorem u1229 : Upper (D 1) (R 1) [112,272,34,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1229
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1230 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 38 137 144 96 78 142 270), lower := (rows 113 274 38 137 144 96 64 128 256), losses := [] }

theorem u1230 : Upper (D 1) (R 1) [112,272,34,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1230
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1231 : PairBound 9 := { available := 76, camps := [], pairs := [], upper := (rows 113 274 38 138 144 33 76 204 332), lower := (rows 113 274 38 138 144 33 64 128 256), losses := [] }

theorem u1231 : Upper (D 1) (R 1) [112,272,34,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1231
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1232 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 113 274 38 138 144 36 73 201 329), lower := (rows 113 274 38 138 144 36 64 128 256), losses := [] }

theorem u1232 : Upper (D 1) (R 1) [112,272,34,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1232
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1233 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 113 274 38 138 144 40 69 197 325), lower := (rows 113 274 38 138 144 40 64 128 256), losses := [] }

theorem u1233 : Upper (D 1) (R 1) [112,272,34,130,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1233
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1234 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 38 138 144 96 77 141 269), lower := (rows 113 274 38 138 144 96 64 128 256), losses := [] }

theorem u1234 : Upper (D 1) (R 1) [112,272,34,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1234
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1235 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 113 274 38 140 144 33 74 202 330), lower := (rows 113 274 38 140 144 33 64 128 256), losses := [] }

theorem u1235 : Upper (D 1) (R 1) [112,272,34,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1235
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1236 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 113 274 38 140 144 34 73 201 329), lower := (rows 113 274 38 140 144 34 64 128 256), losses := [] }

theorem u1236 : Upper (D 1) (R 1) [112,272,34,132,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1236
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1237 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 274 38 140 144 40 67 195 323), lower := (rows 113 274 38 140 144 40 64 128 256), losses := [] }

theorem u1237 : Upper (D 1) (R 1) [112,272,34,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1237
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1238 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 38 140 144 96 75 139 267), lower := (rows 113 274 38 140 144 96 64 128 256), losses := [] }

theorem u1238 : Upper (D 1) (R 1) [112,272,34,132,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1238
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1239 : PairBound 9 := { available := 14, camps := [], pairs := [], upper := (rows 113 274 38 200 144 33 78 142 270), lower := (rows 113 274 38 200 144 33 64 128 256), losses := [] }

theorem u1239 : Upper (D 1) (R 1) [112,272,34,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1239
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1240 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 113 274 38 200 144 34 77 141 269), lower := (rows 113 274 38 200 144 34 64 128 256), losses := [] }

theorem u1240 : Upper (D 1) (R 1) [112,272,34,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1240
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1241 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 113 274 38 200 144 36 75 139 267), lower := (rows 113 274 38 200 144 36 64 128 256), losses := [] }

theorem u1241 : Upper (D 1) (R 1) [112,272,34,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1241
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1242 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 113 274 38 200 144 40 71 135 263), lower := (rows 113 274 38 200 144 40 64 128 256), losses := [] }

theorem u1242 : Upper (D 1) (R 1) [112,272,34,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1242
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1243 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 274 44 138 144 33 70 198 326), lower := (rows 113 274 44 138 144 33 64 128 256), losses := [] }

theorem u1243 : Upper (D 1) (R 1) [112,272,40,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1243
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1244 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 113 274 44 138 144 34 69 197 325), lower := (rows 113 274 44 138 144 34 64 128 256), losses := [] }

theorem u1244 : Upper (D 1) (R 1) [112,272,40,130,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1244
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1245 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 274 44 138 144 36 67 195 323), lower := (rows 113 274 44 138 144 36 64 128 256), losses := [] }

theorem u1245 : Upper (D 1) (R 1) [112,272,40,130,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1245
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1246 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 274 44 138 144 96 71 135 263), lower := (rows 113 274 44 138 144 96 64 128 256), losses := [] }

theorem u1246 : Upper (D 1) (R 1) [112,272,40,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1246
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1247 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 113 274 44 200 144 33 70 134 262), lower := (rows 113 274 44 200 144 33 64 128 256), losses := [] }

theorem u1247 : Upper (D 1) (R 1) [112,272,40,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1247
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1248 : Route 9 := (fun mask => (mask,id))

def c1248 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1248 : Upper (D 1) (R 1) [112,272,40,192,128,2] 13 := by
  apply FastRouting.sound _ _ [112,272,40,192,128,2] 13 (by decide) (choices 1) [1,2,4] r1248 c1248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u155
  · exact u156
  · exact u157

def b1249 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 113 274 44 200 144 36 67 131 259), lower := (rows 113 274 44 200 144 36 64 128 256), losses := [] }

theorem u1249 : Upper (D 1) (R 1) [112,272,40,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1249
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1250 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 386 13 14 18 160 112 240 368), lower := (rows 113 386 13 14 18 160 64 128 256), losses := [] }

theorem u1250 : Upper (D 1) (R 1) [112,384,9,6,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1250
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1251 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5)], upper := (rows 113 386 13 14 48 160 82 210 338), lower := (rows 113 386 13 14 48 160 64 128 256), losses := [] }

theorem u1251 : Upper (D 1) (R 1) [112,384,9,6,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1251
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1252 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 113 386 13 14 80 160 114 178 306), lower := (rows 113 386 13 14 80 160 64 128 256), losses := [] }

theorem u1252 : Upper (D 1) (R 1) [112,384,9,6,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1252
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1253 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 386 28 168 18 33 70 198 326), lower := (rows 113 386 28 168 18 33 64 128 256), losses := [] }

theorem u1253 : Upper (D 1) (R 1) [112,384,24,160,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1253
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1254 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 28 168 18 34 69 197 325), lower := (rows 113 386 28 168 18 34 64 128 256), losses := [] }

theorem u1254 : Upper (D 1) (R 1) [112,384,24,160,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1254
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1255 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 386 28 168 18 36 67 195 323), lower := (rows 113 386 28 168 18 36 64 128 256), losses := [] }

theorem u1255 : Upper (D 1) (R 1) [112,384,24,160,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1255
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1256 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 386 28 168 18 96 71 135 263), lower := (rows 113 386 28 168 18 96 64 128 256), losses := [] }

theorem u1256 : Upper (D 1) (R 1) [112,384,24,160,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1256
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1257 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 212, targets := 2 }], pairs := [(2,1)], upper := (rows 263 11 52 88 144 34 224 224 480), lower := (rows 263 11 52 88 144 34 64 128 256), losses := [] }

theorem u1257 : Upper (D 1) (R 1) [262,9,48,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1257
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1258 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 263 11 52 88 144 96 226 162 418), lower := (rows 263 11 52 88 144 96 64 128 256), losses := [] }

theorem u1258 : Upper (D 1) (R 1) [262,9,48,80,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1258
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1259 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 263 11 52 88 144 160 98 226 354), lower := (rows 263 11 52 88 144 160 64 128 256), losses := [] }

theorem u1259 : Upper (D 1) (R 1) [262,9,48,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1259
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1259
end Delivery.IrregularNine14.P01
