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

def b1260 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 263 11 52 200 18 96 240 176 432), lower := (rows 263 11 52 200 18 96 64 128 256), losses := [] }

theorem u1260 : Upper (D 1) (R 1) [262,9,48,192,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1260
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1261 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 263 11 52 200 48 96 210 146 402), lower := (rows 263 11 52 200 48 96 64 128 256), losses := [] }

theorem u1261 : Upper (D 1) (R 1) [262,9,48,192,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1261
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1262 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 52, targets := 2 }], pairs := [(2,1)], upper := (rows 263 11 52 200 80 160 114 178 306), lower := (rows 263 11 52 200 80 160 64 128 256), losses := [] }

theorem u1262 : Upper (D 1) (R 1) [262,9,48,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1262
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1263 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 220, targets := 2 }], pairs := [(2,1)], upper := (rows 263 19 44 88 144 34 224 224 480), lower := (rows 263 19 44 88 144 34 64 128 256), losses := [] }

theorem u1263 : Upper (D 1) (R 1) [262,17,40,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1263
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1264 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 263 19 44 88 144 96 226 162 418), lower := (rows 263 19 44 88 144 96 64 128 256), losses := [] }

theorem u1264 : Upper (D 1) (R 1) [262,17,40,80,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1264
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1265 : PairBound 9 := { available := 98, camps := [], pairs := [(2,1)], upper := (rows 263 19 44 88 144 160 98 226 354), lower := (rows 263 19 44 88 144 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 176 176 64 128 256), good := (rows 261 49 60 124 176 176 64 176 256) }] }

theorem u1265 : Upper (D 1) (R 1) [262,17,40,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1265
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1266 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 220, targets := 2 }], pairs := [(2,1)], upper := (rows 263 19 44 200 80 34 240 176 432), lower := (rows 263 19 44 200 80 34 64 128 256), losses := [] }

theorem u1266 : Upper (D 1) (R 1) [262,17,40,192,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1266
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1267 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 52, targets := 2 }], pairs := [(2,1)], upper := (rows 263 19 44 200 80 48 226 162 418), lower := (rows 263 19 44 200 80 48 64 128 256), losses := [] }

theorem u1267 : Upper (D 1) (R 1) [262,17,40,192,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1267
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1268 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 263 19 44 200 80 160 114 178 306), lower := (rows 263 19 44 200 80 160 64 128 256), losses := [] }

theorem u1268 : Upper (D 1) (R 1) [262,17,40,192,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1268
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1269 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 263 19 100 56 144 34 200 200 456), lower := (rows 263 19 100 56 144 34 64 128 256), losses := [] }

theorem u1269 : Upper (D 1) (R 1) [262,17,96,48,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1269
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1270 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 263 19 100 56 144 40 194 194 450), lower := (rows 263 19 100 56 144 40 64 128 256), losses := [] }

theorem u1270 : Upper (D 1) (R 1) [262,17,96,48,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1270
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1271 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 263 19 100 56 144 96 202 138 394), lower := (rows 263 19 100 56 144 96 64 128 256), losses := [] }

theorem u1271 : Upper (D 1) (R 1) [262,17,96,48,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1271
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1272 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 263 19 100 56 144 160 74 202 330), lower := (rows 263 19 100 56 144 160 64 128 256), losses := [] }

theorem u1272 : Upper (D 1) (R 1) [262,17,96,48,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1272
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1273 : PairBound 9 := { available := 88, camps := [{ cop := 5, region := 220, targets := 2 }], pairs := [(2,1)], upper := (rows 263 19 100 168 144 34 88 216 344), lower := (rows 263 19 100 168 144 34 64 128 256), losses := [] }

theorem u1273 : Upper (D 1) (R 1) [262,17,96,160,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1273
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1274 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 263 19 100 168 144 40 82 210 338), lower := (rows 263 19 100 168 144 40 64 128 256), losses := [] }

theorem u1274 : Upper (D 1) (R 1) [262,17,96,160,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1274
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1275 : PairBound 9 := { available := 74, camps := [{ cop := 4, region := 40, targets := 2 }], pairs := [(3,1)], upper := (rows 263 19 100 168 144 48 74 202 330), lower := (rows 263 19 100 168 144 48 64 128 256), losses := [] }

theorem u1275 : Upper (D 1) (R 1) [262,17,96,160,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1275
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1276 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 263 19 100 168 144 96 90 154 282), lower := (rows 263 19 100 168 144 96 64 128 256), losses := [] }

theorem u1276 : Upper (D 1) (R 1) [262,17,96,160,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1276
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1277 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 263 26 100 168 80 33 210 146 402), lower := (rows 263 26 100 168 80 33 64 128 256), losses := [] }

theorem u1277 : Upper (D 1) (R 1) [262,24,96,160,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1277
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1278 : Route 9 := (fun mask => (mask,id))

def c1278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1278 : Upper (D 1) (R 1) [262,24,96,160,64,2] 13 := by
  apply FastRouting.sound _ _ [262,24,96,160,64,2] 13 (by decide) (choices 1) [1,16,128] r1278 c1278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u158
  · exact u159
  · exact u160

def b1279 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 263 26 100 168 80 48 195 131 387), lower := (rows 263 26 100 168 80 48 64 128 256), losses := [] }

theorem u1279 : Upper (D 1) (R 1) [262,24,96,160,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1279
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1280 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 263 26 100 168 80 160 83 147 275), lower := (rows 263 26 100 168 80 160 64 128 256), losses := [] }

theorem u1280 : Upper (D 1) (R 1) [262,24,96,160,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1280
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1281 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 13 74 48 160 208 208 464), lower := (rows 263 50 13 74 48 160 64 128 256), losses := [] }

theorem u1281 : Upper (D 1) (R 1) [262,48,9,66,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1281
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1282 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 13 74 80 160 240 176 432), lower := (rows 263 50 13 74 80 160 64 128 256), losses := [] }

theorem u1282 : Upper (D 1) (R 1) [262,48,9,66,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1282
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1283 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 263 50 13 74 144 160 112 240 368), lower := (rows 263 50 13 74 144 160 64 128 256), losses := [] }

theorem u1283 : Upper (D 1) (R 1) [262,48,9,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1283
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1284 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 13 88 144 34 224 224 480), lower := (rows 263 50 13 88 144 34 64 128 256), losses := [] }

theorem u1284 : Upper (D 1) (R 1) [262,48,9,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1284
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1285 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 263 50 13 88 144 96 226 162 418), lower := (rows 263 50 13 88 144 96 64 128 256), losses := [] }

theorem u1285 : Upper (D 1) (R 1) [262,48,9,80,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1285
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1286 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 263 50 13 88 144 160 98 226 354), lower := (rows 263 50 13 88 144 160 64 128 256), losses := [] }

theorem u1286 : Upper (D 1) (R 1) [262,48,9,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1286
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1287 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 263 50 69 138 24 160 112 240 368), lower := (rows 263 50 69 138 24 160 64 128 256), losses := [] }

theorem u1287 : Upper (D 1) (R 1) [262,48,65,130,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1287
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1288 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 69 138 48 160 88 216 344), lower := (rows 263 50 69 138 48 160 64 128 256), losses := [] }

theorem u1288 : Upper (D 1) (R 1) [262,48,65,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1288
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1289 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 69 138 80 160 120 184 312), lower := (rows 263 50 69 138 80 160 64 128 256), losses := [] }

theorem u1289 : Upper (D 1) (R 1) [262,48,65,130,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1289
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1290 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 263 50 76 138 17 96 240 176 432), lower := (rows 263 50 76 138 17 96 64 128 256), losses := [] }

theorem u1290 : Upper (D 1) (R 1) [262,48,72,130,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1290
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1291 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 263 50 76 138 17 160 112 240 368), lower := (rows 263 50 76 138 17 160 64 128 256), losses := [] }

theorem u1291 : Upper (D 1) (R 1) [262,48,72,130,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1291
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1292 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 76 138 48 96 209 145 401), lower := (rows 263 50 76 138 48 96 64 128 256), losses := [] }

theorem u1292 : Upper (D 1) (R 1) [262,48,72,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1292
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1293 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 76 138 48 160 81 209 337), lower := (rows 263 50 76 138 48 160 64 128 256), losses := [] }

theorem u1293 : Upper (D 1) (R 1) [262,48,72,130,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1293
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1294 : Route 9 := (fun mask => (mask,id))

def c1294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1294 : Upper (D 1) (R 1) [262,48,72,130,64,128] 13 := by
  apply FastRouting.sound _ _ [262,48,72,130,64,128] 13 (by decide) (choices 1) [1,16,32] r1294 c1294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u161
  · exact u162
  · exact u163

def b1295 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 263 50 76 152 80 33 226 162 418), lower := (rows 263 50 76 152 80 33 64 128 256), losses := [] }

theorem u1295 : Upper (D 1) (R 1) [262,48,72,144,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1295
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1296 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 76 152 80 34 225 161 417), lower := (rows 263 50 76 152 80 34 64 128 256), losses := [] }

theorem u1296 : Upper (D 1) (R 1) [262,48,72,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1296
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1297 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 76 152 80 160 99 163 291), lower := (rows 263 50 76 152 80 160 64 128 256), losses := [] }

theorem u1297 : Upper (D 1) (R 1) [262,48,72,144,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1297
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1298 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 263 50 196 74 17 160 120 184 312), lower := (rows 263 50 196 74 17 160 64 128 256), losses := [] }

theorem u1298 : Upper (D 1) (R 1) [262,48,192,66,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1298
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1299 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 263 50 196 74 24 160 113 177 305), lower := (rows 263 50 196 74 24 160 64 128 256), losses := [] }

theorem u1299 : Upper (D 1) (R 1) [262,48,192,66,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1299
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1300 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 196 74 48 160 89 153 281), lower := (rows 263 50 196 74 48 160 64 128 256), losses := [] }

theorem u1300 : Upper (D 1) (R 1) [262,48,192,66,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1300
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1301 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 269 19 38 74 144 48 224 224 480), lower := (rows 269 19 38 74 144 48 64 128 256), losses := [] }

theorem u1301 : Upper (D 1) (R 1) [268,17,34,66,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1301
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1302 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 36, targets := 16 }], pairs := [(2,4)], upper := (rows 269 19 38 74 144 96 240 176 432), lower := (rows 269 19 38 74 144 96 64 128 256), losses := [] }

theorem u1302 : Upper (D 1) (R 1) [268,17,34,66,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1302
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1303 : PairBound 9 := { available := 112, camps := [], pairs := [(2,4)], upper := (rows 269 19 38 74 144 160 112 240 368), lower := (rows 269 19 38 74 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 2 6 8 0 176 64 128 256), good := (rows 269 39 38 78 160 160 64 160 256) }] }

theorem u1303 : Upper (D 1) (R 1) [268,17,34,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1303
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1304 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 269 50 7 74 48 160 208 208 464), lower := (rows 269 50 7 74 48 160 64 128 256), losses := [] }

theorem u1304 : Upper (D 1) (R 1) [268,48,3,66,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1304
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1305 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 7 74 80 160 240 176 432), lower := (rows 269 50 7 74 80 160 64 128 256), losses := [] }

theorem u1305 : Upper (D 1) (R 1) [268,48,3,66,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1305
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1306 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 269 50 7 74 144 160 112 240 368), lower := (rows 269 50 7 74 144 160 64 128 256), losses := [] }

theorem u1306 : Upper (D 1) (R 1) [268,48,3,66,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1306
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1307 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 7 88 144 34 224 224 480), lower := (rows 269 50 7 88 144 34 64 128 256), losses := [] }

theorem u1307 : Upper (D 1) (R 1) [268,48,3,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1307
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1308 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 269 50 7 88 144 96 226 162 418), lower := (rows 269 50 7 88 144 96 64 128 256), losses := [] }

theorem u1308 : Upper (D 1) (R 1) [268,48,3,80,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1308
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1309 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 269 50 7 88 144 160 98 226 354), lower := (rows 269 50 7 88 144 160 64 128 256), losses := [] }

theorem u1309 : Upper (D 1) (R 1) [268,48,3,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1309
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1310 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 269 50 70 138 17 96 240 176 432), lower := (rows 269 50 70 138 17 96 64 128 256), losses := [] }

theorem u1310 : Upper (D 1) (R 1) [268,48,66,130,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1310
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1311 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 269 50 70 138 48 96 209 145 401), lower := (rows 269 50 70 138 48 96 64 128 256), losses := [] }

theorem u1311 : Upper (D 1) (R 1) [268,48,66,130,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1311
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1312 : Route 9 := (fun mask => (mask,id))

def c1312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1312 : Upper (D 1) (R 1) [268,48,66,130,64,128] 13 := by
  apply FastRouting.sound _ _ [268,48,66,130,64,128] 13 (by decide) (choices 1) [1,16,32] r1312 c1312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u164
  · exact u165
  · exact u166

def b1313 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 269 50 70 152 80 33 226 162 418), lower := (rows 269 50 70 152 80 33 64 128 256), losses := [] }

theorem u1313 : Upper (D 1) (R 1) [268,48,66,144,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1313
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1314 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 70 152 80 34 225 161 417), lower := (rows 269 50 70 152 80 34 64 128 256), losses := [] }

theorem u1314 : Upper (D 1) (R 1) [268,48,66,144,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1314
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1315 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 70 152 80 160 99 163 291), lower := (rows 269 50 70 152 80 160 64 128 256), losses := [] }

theorem u1315 : Upper (D 1) (R 1) [268,48,66,144,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1315
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1316 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 220, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 44 88 144 34 224 224 480), lower := (rows 275 7 44 88 144 34 64 128 256), losses := [] }

theorem u1316 : Upper (D 1) (R 1) [274,5,40,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1316
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1317 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 44 88 144 96 226 162 418), lower := (rows 275 7 44 88 144 96 64 128 256), losses := [] }

theorem u1317 : Upper (D 1) (R 1) [274,5,40,80,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1317
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1318 : PairBound 9 := { available := 98, camps := [], pairs := [(2,1)], upper := (rows 275 7 44 88 144 160 98 226 354), lower := (rows 275 7 44 88 144 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 176 176 64 128 256), good := (rows 305 5 60 124 176 176 64 176 256) }] }

theorem u1318 : Upper (D 1) (R 1) [274,5,40,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1318
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1319 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 220, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 44 200 80 34 240 176 432), lower := (rows 275 7 44 200 80 34 64 128 256), losses := [] }

theorem u1319 : Upper (D 1) (R 1) [274,5,40,192,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1319
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1319
end Delivery.IrregularNine14.P01
