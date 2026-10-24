import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1200 : PairBound 9 := { available := 34, camps := [], pairs := [(0,2),(1,2)], upper := (rows 19 67 140 268 52 33 72 162 290), lower := (rows 19 67 140 268 52 33 72 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 51 76 147 275), good := (rows 435 483 200 328 499 417 72 128 256) }] }

theorem u1200 : Upper (D 5) (R 5) [18,65,136,260,36,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1200
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1201 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 19 67 140 268 52 33 96 138 266), lower := (rows 19 67 140 268 52 33 96 128 256), losses := [] }

theorem u1201 : Upper (D 5) (R 5) [18,65,136,260,36,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1201
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1202 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 140 268 52 34 65 168 296), lower := (rows 19 67 140 268 52 34 65 128 256), losses := [] }

theorem u1202 : Upper (D 5) (R 5) [18,65,136,260,36,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1202
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1203 : PairBound 9 := { available := 33, camps := [], pairs := [(0,2),(1,2)], upper := (rows 19 67 140 268 52 34 72 161 289), lower := (rows 19 67 140 268 52 34 72 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 51 76 147 275), good := (rows 435 483 200 328 499 418 72 128 256) }] }

theorem u1203 : Upper (D 5) (R 5) [18,65,136,260,36,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1203
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1204 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 19 67 140 268 52 34 96 137 265), lower := (rows 19 67 140 268 52 34 96 128 256), losses := [] }

theorem u1204 : Upper (D 5) (R 5) [18,65,136,260,36,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1204
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1205 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 140 296 52 33 66 140 268), lower := (rows 19 67 140 296 52 33 66 128 256), losses := [] }

theorem u1205 : Upper (D 5) (R 5) [18,65,136,288,36,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1205
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1206 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 115, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 67 140 296 52 33 68 138 266), lower := (rows 19 67 140 296 52 33 68 128 256), losses := [] }

theorem u1206 : Upper (D 5) (R 5) [18,65,136,288,36,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1206
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1207 : PairBound 9 := { available := 6, camps := [], pairs := [(0,2),(1,2)], upper := (rows 19 67 140 296 52 33 72 134 262), lower := (rows 19 67 140 296 52 33 72 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 51 76 128 256), good := (rows 51 99 200 360 115 33 72 128 256) }] }

theorem u1207 : Upper (D 5) (R 5) [18,65,136,288,36,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1207
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1208 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 67 140 296 52 34 65 140 268), lower := (rows 19 67 140 296 52 34 65 128 256), losses := [] }

theorem u1208 : Upper (D 5) (R 5) [18,65,136,288,36,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1208
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1209 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 115, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 67 140 296 52 34 68 137 265), lower := (rows 19 67 140 296 52 34 68 128 256), losses := [] }

theorem u1209 : Upper (D 5) (R 5) [18,65,136,288,36,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1209
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1210 : PairBound 9 := { available := 5, camps := [], pairs := [(0,2),(1,2)], upper := (rows 19 67 140 296 52 34 72 133 261), lower := (rows 19 67 140 296 52 34 72 128 256), losses := [{ target := 2, region := (rows 17 18 0 8 16 51 76 128 256), good := (rows 51 99 200 360 115 34 72 128 256) }] }

theorem u1210 : Upper (D 5) (R 5) [18,65,136,288,36,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1210
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1211 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 296, targets := 1 }], pairs := [(3,0)], upper := (rows 19 70 37 42 152 288 65 140 268), lower := (rows 19 70 37 42 152 288 65 128 256), losses := [] }

theorem u1211 : Upper (D 5) (R 5) [18,68,33,34,136,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1211
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1212 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 441, targets := 4 }], pairs := [(0,2)], upper := (rows 19 70 37 42 152 288 68 137 265), lower := (rows 19 70 37 42 152 288 68 128 256), losses := [] }

theorem u1212 : Upper (D 5) (R 5) [18,68,33,34,136,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1212
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1213 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 292, targets := 2 }], pairs := [(2,1)], upper := (rows 19 70 37 42 152 288 72 133 261), lower := (rows 19 70 37 42 152 288 72 128 256), losses := [] }

theorem u1213 : Upper (D 5) (R 5) [18,68,33,34,136,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1213
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1214 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 70 37 138 276 40 65 168 296), lower := (rows 19 70 37 138 276 40 65 128 256), losses := [] }

theorem u1214 : Upper (D 5) (R 5) [18,68,33,130,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1214
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1215 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 272, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 19 70 37 138 276 40 72 161 289), lower := (rows 19 70 37 138 276 40 72 128 256), losses := [] }

theorem u1215 : Upper (D 5) (R 5) [18,68,33,130,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1215
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1216 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 70 37 138 276 40 96 137 265), lower := (rows 19 70 37 138 276 40 96 128 256), losses := [] }

theorem u1216 : Upper (D 5) (R 5) [18,68,33,130,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1216
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1217 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 70, targets := 8 }], pairs := [(1,3)], upper := (rows 19 70 38 41 152 288 65 140 268), lower := (rows 19 70 38 41 152 288 65 128 256), losses := [] }

theorem u1217 : Upper (D 5) (R 5) [18,68,34,33,136,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1217
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1218 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1)], upper := (rows 19 70 38 41 152 288 68 137 265), lower := (rows 19 70 38 41 152 288 68 128 256), losses := [] }

theorem u1218 : Upper (D 5) (R 5) [18,68,34,33,136,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1218
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1219 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 19 70 38 41 152 288 72 133 261), lower := (rows 19 70 38 41 152 288 72 128 256), losses := [] }

theorem u1219 : Upper (D 5) (R 5) [18,68,34,33,136,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1219
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1220 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3)], upper := (rows 19 70 38 137 56 288 65 140 268), lower := (rows 19 70 38 137 56 288 65 128 256), losses := [] }

theorem u1220 : Upper (D 5) (R 5) [18,68,34,129,40,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1220
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1221 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1)], upper := (rows 19 70 38 137 56 288 68 137 265), lower := (rows 19 70 38 137 56 288 68 128 256), losses := [] }

theorem u1221 : Upper (D 5) (R 5) [18,68,34,129,40,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1221
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1222 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 19 70 38 137 56 288 72 133 261), lower := (rows 19 70 38 137 56 288 72 128 256), losses := [] }

theorem u1222 : Upper (D 5) (R 5) [18,68,34,129,40,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1222
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1223 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 168, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 137 280 33 68 168 296), lower := (rows 19 70 38 137 280 33 68 128 256), losses := [] }

theorem u1223 : Upper (D 5) (R 5) [18,68,34,129,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1223
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1224 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 36, targets := 8 }], pairs := [(1,3),(2,3)], upper := (rows 19 70 38 137 280 33 72 164 292), lower := (rows 19 70 38 137 280 33 72 128 256), losses := [{ target := 3, region := (rows 1 66 69 0 16 41 64 237 365), good := (rows 439 454 422 421 432 421 486 128 256) }] }

theorem u1224 : Upper (D 5) (R 5) [18,68,34,129,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1224
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1225 : PairBound 9 := { available := 12, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 137 280 33 96 140 268), lower := (rows 19 70 38 137 280 33 96 128 256), losses := [] }

theorem u1225 : Upper (D 5) (R 5) [18,68,34,129,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1225
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1226 : PairBound 9 := { available := 36, camps := [], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 137 280 40 65 164 292), lower := (rows 19 70 38 137 280 40 65 128 256), losses := [{ target := 0, region := (rows 0 66 5 8 56 56 64 141 269), good := (rows 438 454 438 444 440 440 454 128 256) }] }

theorem u1226 : Upper (D 5) (R 5) [18,68,34,129,264,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1226
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1227 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 168, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 137 280 40 68 161 289), lower := (rows 19 70 38 137 280 40 68 128 256), losses := [] }

theorem u1227 : Upper (D 5) (R 5) [18,68,34,129,264,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1227
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1228 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 137 280 40 96 133 261), lower := (rows 19 70 38 137 280 40 96 128 256), losses := [] }

theorem u1228 : Upper (D 5) (R 5) [18,68,34,129,264,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1228
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1229 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 136, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 137 304 33 68 136 264), lower := (rows 19 70 38 137 304 33 68 128 256), losses := [] }

theorem u1229 : Upper (D 5) (R 5) [18,68,34,129,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1229
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1230 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 36, targets := 8 }], pairs := [(1,3),(2,3)], upper := (rows 19 70 38 137 304 33 72 140 268), lower := (rows 19 70 38 137 304 33 72 128 256), losses := [{ target := 3, region := (rows 1 66 69 0 16 41 64 128 256), good := (rows 55 70 38 165 304 37 102 128 256) }] }

theorem u1230 : Upper (D 5) (R 5) [18,68,34,129,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1230
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1231 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 70 38 137 304 40 65 140 268), lower := (rows 19 70 38 137 304 40 65 128 256), losses := [] }

theorem u1231 : Upper (D 5) (R 5) [18,68,34,129,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1231
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1232 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 137 304 40 68 137 265), lower := (rows 19 70 38 137 304 40 68 128 256), losses := [] }

theorem u1232 : Upper (D 5) (R 5) [18,68,34,129,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1232
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1233 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 273, targets := 8 }], pairs := [(0,3),(4,3)], upper := (rows 19 70 38 137 304 40 72 133 261), lower := (rows 19 70 38 137 304 40 72 128 256), losses := [] }

theorem u1233 : Upper (D 5) (R 5) [18,68,34,129,288,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1233
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1234 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 70 38 140 25 40 65 416 288), lower := (rows 19 70 38 140 25 40 65 128 256), losses := [] }

theorem u1234 : Upper (D 5) (R 5) [18,68,34,132,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1234
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1235 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 140 25 40 96 385 257), lower := (rows 19 70 38 140 25 40 96 128 256), losses := [] }

theorem u1235 : Upper (D 5) (R 5) [18,68,34,132,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1235
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1236 : PairBound 9 := { available := 33, camps := [], pairs := [(2,0)], upper := (rows 19 70 38 140 25 40 320 161 289), lower := (rows 19 70 38 140 25 40 320 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 16 56 320 128 256), good := (rows 54 70 38 172 60 40 320 128 320) }] }

theorem u1236 : Upper (D 5) (R 5) [18,68,34,132,9,8,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1236
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1237 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5)], upper := (rows 19 70 38 140 25 288 65 168 296), lower := (rows 19 70 38 140 25 288 65 128 256), losses := [] }

theorem u1237 : Upper (D 5) (R 5) [18,68,34,132,9,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1237
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1238 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 83, targets := 32 }], pairs := [(0,5)], upper := (rows 19 70 38 140 25 288 72 161 289), lower := (rows 19 70 38 140 25 288 72 128 256), losses := [] }

theorem u1238 : Upper (D 5) (R 5) [18,68,34,132,9,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1238
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1239 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 19 70 38 140 25 288 96 137 265), lower := (rows 19 70 38 140 25 288 96 128 256), losses := [] }

theorem u1239 : Upper (D 5) (R 5) [18,68,34,132,9,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1239
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1240 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 392, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 38 140 56 33 65 392 264), lower := (rows 19 70 38 140 56 33 65 128 256), losses := [] }

theorem u1240 : Upper (D 5) (R 5) [18,68,34,132,40,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1240
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1241 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 19 70 38 140 56 33 72 385 257), lower := (rows 19 70 38 140 56 33 72 128 256), losses := [] }

theorem u1241 : Upper (D 5) (R 5) [18,68,34,132,40,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1241
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1242 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 36, targets := 8 }], pairs := [(2,3)], upper := (rows 19 70 38 140 56 33 320 137 265), lower := (rows 19 70 38 140 56 33 320 128 256), losses := [] }

theorem u1242 : Upper (D 5) (R 5) [18,68,34,132,40,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1242
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1243 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3)], upper := (rows 19 70 38 140 56 288 65 137 265), lower := (rows 19 70 38 140 56 288 65 128 256), losses := [] }

theorem u1243 : Upper (D 5) (R 5) [18,68,34,132,40,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1243
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1244 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 19 70 38 140 56 288 72 129 257), lower := (rows 19 70 38 140 56 288 72 128 256), losses := [] }

theorem u1244 : Upper (D 5) (R 5) [18,68,34,132,40,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1244
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1245 : PairBound 9 := { available := 40, camps := [{ cop := 6, region := 174, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 140 273 40 65 168 296), lower := (rows 19 70 38 140 273 40 65 128 256), losses := [] }

theorem u1245 : Upper (D 5) (R 5) [18,68,34,132,257,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1245
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1246 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 110, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 140 273 40 72 161 289), lower := (rows 19 70 38 140 273 40 72 128 256), losses := [] }

theorem u1246 : Upper (D 5) (R 5) [18,68,34,132,257,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1246
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1247 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 140 273 40 96 137 265), lower := (rows 19 70 38 140 273 40 96 128 256), losses := [] }

theorem u1247 : Upper (D 5) (R 5) [18,68,34,132,257,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1247
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1248 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 38 140 280 33 65 168 296), lower := (rows 19 70 38 140 280 33 65 128 256), losses := [] }

theorem u1248 : Upper (D 5) (R 5) [18,68,34,132,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1248
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1249 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 19 70 38 140 280 33 72 161 289), lower := (rows 19 70 38 140 280 33 72 128 256), losses := [] }

theorem u1249 : Upper (D 5) (R 5) [18,68,34,132,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1249
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1250 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 70, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 140 280 33 96 137 265), lower := (rows 19 70 38 140 280 33 96 128 256), losses := [] }

theorem u1250 : Upper (D 5) (R 5) [18,68,34,132,264,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1250
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1251 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 38 140 304 33 65 136 264), lower := (rows 19 70 38 140 304 33 65 128 256), losses := [] }

theorem u1251 : Upper (D 5) (R 5) [18,68,34,132,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1251
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1252 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 19 70 38 140 304 33 72 137 265), lower := (rows 19 70 38 140 304 33 72 128 256), losses := [] }

theorem u1252 : Upper (D 5) (R 5) [18,68,34,132,288,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1252
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1253 : PairBound 9 := { available := 12, camps := [{ cop := 6, region := 430, targets := 1 }], pairs := [(1,0)], upper := (rows 19 70 38 168 25 288 65 140 268), lower := (rows 19 70 38 168 25 288 65 128 256), losses := [] }

theorem u1253 : Upper (D 5) (R 5) [18,68,34,160,9,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1253
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1254 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 424, targets := 2 }], pairs := [(3,1)], upper := (rows 19 70 38 168 25 288 68 137 265), lower := (rows 19 70 38 168 25 288 68 128 256), losses := [] }

theorem u1254 : Upper (D 5) (R 5) [18,68,34,160,9,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1254
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1255 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 19 70 38 168 25 288 72 133 261), lower := (rows 19 70 38 168 25 288 72 128 256), losses := [] }

theorem u1255 : Upper (D 5) (R 5) [18,68,34,160,9,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1255
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1256 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 136, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 38 168 280 33 65 140 268), lower := (rows 19 70 38 168 280 33 65 128 256), losses := [] }

theorem u1256 : Upper (D 5) (R 5) [18,68,34,160,264,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1256
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1257 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 168, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 168 280 33 68 137 265), lower := (rows 19 70 38 168 280 33 68 128 256), losses := [] }

theorem u1257 : Upper (D 5) (R 5) [18,68,34,160,264,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1257
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1258 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 168 280 33 72 133 261), lower := (rows 19 70 38 168 280 33 72 128 256), losses := [] }

theorem u1258 : Upper (D 5) (R 5) [18,68,34,160,264,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1258
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1259 : PairBound 9 := { available := 36, camps := [{ cop := 6, region := 430, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 392 25 40 65 164 292), lower := (rows 19 70 38 392 25 40 65 128 256), losses := [] }

theorem u1259 : Upper (D 5) (R 5) [18,68,34,384,9,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1259
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1259
end Delivery.IrregularNine14.P05
