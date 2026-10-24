import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1200 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 35 67 133 152 304 40 69 197 325), lower := (rows 35 67 133 152 304 40 64 128 256), losses := [] }

theorem u1200 : Upper (D 3) (R 3) [34,65,129,144,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1200
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1201 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 133 152 304 96 77 141 269), lower := (rows 35 67 133 152 304 96 64 128 256), losses := [] }

theorem u1201 : Upper (D 3) (R 3) [34,65,129,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1201
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1202 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 133 152 336 33 108 172 300), lower := (rows 35 67 133 152 336 33 64 128 256), losses := [] }

theorem u1202 : Upper (D 3) (R 3) [34,65,129,144,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1202
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1203 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 67 133 152 336 36 105 169 297), lower := (rows 35 67 133 152 336 36 64 128 256), losses := [] }

theorem u1203 : Upper (D 3) (R 3) [34,65,129,144,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1203
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1204 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 133 152 336 40 101 165 293), lower := (rows 35 67 133 152 336 40 64 128 256), losses := [] }

theorem u1204 : Upper (D 3) (R 3) [34,65,129,144,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1204
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1205 : PairBound 9 := { available := 88, camps := [], pairs := [], upper := (rows 35 67 133 168 273 36 88 216 344), lower := (rows 35 67 133 168 273 36 64 128 256), losses := [] }

theorem u1205 : Upper (D 3) (R 3) [34,65,129,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1205
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1206 : PairBound 9 := { available := 84, camps := [], pairs := [], upper := (rows 35 67 133 168 273 40 84 212 340), lower := (rows 35 67 133 168 273 40 64 128 256), losses := [] }

theorem u1206 : Upper (D 3) (R 3) [34,65,129,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1206
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1207 : PairBound 9 := { available := 76, camps := [], pairs := [], upper := (rows 35 67 133 168 273 48 76 204 332), lower := (rows 35 67 133 168 273 48 64 128 256), losses := [] }

theorem u1207 : Upper (D 3) (R 3) [34,65,129,160,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1207
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1208 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 133 168 273 96 92 156 284), lower := (rows 35 67 133 168 273 96 64 128 256), losses := [] }

theorem u1208 : Upper (D 3) (R 3) [34,65,129,160,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1208
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1209 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 133 168 276 33 88 216 344), lower := (rows 35 67 133 168 276 33 64 128 256), losses := [] }

theorem u1209 : Upper (D 3) (R 3) [34,65,129,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1209
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1210 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 67 133 168 276 40 81 209 337), lower := (rows 35 67 133 168 276 40 64 128 256), losses := [] }

theorem u1210 : Upper (D 3) (R 3) [34,65,129,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1210
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1211 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 35 67 133 168 276 48 73 201 329), lower := (rows 35 67 133 168 276 48 64 128 256), losses := [] }

theorem u1211 : Upper (D 3) (R 3) [34,65,129,160,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1211
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1212 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 133 168 276 96 89 153 281), lower := (rows 35 67 133 168 276 96 64 128 256), losses := [] }

theorem u1212 : Upper (D 3) (R 3) [34,65,129,160,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1212
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1213 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 133 168 280 33 84 212 340), lower := (rows 35 67 133 168 280 33 64 128 256), losses := [] }

theorem u1213 : Upper (D 3) (R 3) [34,65,129,160,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1213
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1214 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 67 133 168 280 36 81 209 337), lower := (rows 35 67 133 168 280 36 64 128 256), losses := [] }

theorem u1214 : Upper (D 3) (R 3) [34,65,129,160,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1214
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1215 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 35 67 133 168 280 48 69 197 325), lower := (rows 35 67 133 168 280 48 64 128 256), losses := [] }

theorem u1215 : Upper (D 3) (R 3) [34,65,129,160,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1215
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1216 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 133 168 280 96 85 149 277), lower := (rows 35 67 133 168 280 96 64 128 256), losses := [] }

theorem u1216 : Upper (D 3) (R 3) [34,65,129,160,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1216
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1217 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 133 168 336 33 92 156 284), lower := (rows 35 67 133 168 336 33 64 128 256), losses := [] }

theorem u1217 : Upper (D 3) (R 3) [34,65,129,160,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1217
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1218 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 35 67 133 168 336 36 89 153 281), lower := (rows 35 67 133 168 336 36 64 128 256), losses := [] }

theorem u1218 : Upper (D 3) (R 3) [34,65,129,160,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1218
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1219 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 35 67 133 168 336 40 85 149 277), lower := (rows 35 67 133 168 336 40 64 128 256), losses := [] }

theorem u1219 : Upper (D 3) (R 3) [34,65,129,160,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1219
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1220 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 35 67 133 168 336 48 77 141 269), lower := (rows 35 67 133 168 336 48 64 128 256), losses := [] }

theorem u1220 : Upper (D 3) (R 3) [34,65,129,160,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1220
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1221 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 35 67 133 200 273 36 120 184 312), lower := (rows 35 67 133 200 273 36 64 128 256), losses := [] }

theorem u1221 : Upper (D 3) (R 3) [34,65,129,192,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1221
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1222 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 35 67 133 200 273 40 116 180 308), lower := (rows 35 67 133 200 273 40 64 128 256), losses := [] }

theorem u1222 : Upper (D 3) (R 3) [34,65,129,192,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1222
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1223 : PairBound 9 := { available := 44, camps := [], pairs := [], upper := (rows 35 67 133 200 273 48 108 172 300), lower := (rows 35 67 133 200 273 48 64 128 256), losses := [] }

theorem u1223 : Upper (D 3) (R 3) [34,65,129,192,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1223
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1224 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 133 200 276 33 120 184 312), lower := (rows 35 67 133 200 276 33 64 128 256), losses := [] }

theorem u1224 : Upper (D 3) (R 3) [34,65,129,192,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1224
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1225 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 133 200 276 40 113 177 305), lower := (rows 35 67 133 200 276 40 64 128 256), losses := [] }

theorem u1225 : Upper (D 3) (R 3) [34,65,129,192,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1225
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1226 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 67 133 200 276 48 105 169 297), lower := (rows 35 67 133 200 276 48 64 128 256), losses := [] }

theorem u1226 : Upper (D 3) (R 3) [34,65,129,192,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1226
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1227 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 133 200 280 33 116 180 308), lower := (rows 35 67 133 200 280 33 64 128 256), losses := [] }

theorem u1227 : Upper (D 3) (R 3) [34,65,129,192,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1227
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1228 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 133 200 280 36 113 177 305), lower := (rows 35 67 133 200 280 36 64 128 256), losses := [] }

theorem u1228 : Upper (D 3) (R 3) [34,65,129,192,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1228
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1229 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 133 200 280 48 101 165 293), lower := (rows 35 67 133 200 280 48 64 128 256), losses := [] }

theorem u1229 : Upper (D 3) (R 3) [34,65,129,192,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1229
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1230 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 133 200 304 33 92 156 284), lower := (rows 35 67 133 200 304 33 64 128 256), losses := [] }

theorem u1230 : Upper (D 3) (R 3) [34,65,129,192,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1230
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1231 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 35 67 133 200 304 36 89 153 281), lower := (rows 35 67 133 200 304 36 64 128 256), losses := [] }

theorem u1231 : Upper (D 3) (R 3) [34,65,129,192,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1231
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1232 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 35 67 133 200 304 40 85 149 277), lower := (rows 35 67 133 200 304 40 64 128 256), losses := [] }

theorem u1232 : Upper (D 3) (R 3) [34,65,129,192,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1232
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1233 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 35 67 133 200 304 48 77 141 269), lower := (rows 35 67 133 200 304 48 64 128 256), losses := [] }

theorem u1233 : Upper (D 3) (R 3) [34,65,129,192,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1233
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1234 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 140 265 176 33 84 212 340), lower := (rows 35 67 140 265 176 33 64 128 256), losses := [] }

theorem u1234 : Upper (D 3) (R 3) [34,65,136,257,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1234
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1235 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 67 140 265 176 36 81 209 337), lower := (rows 35 67 140 265 176 36 64 128 256), losses := [] }

theorem u1235 : Upper (D 3) (R 3) [34,65,136,257,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1235
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1236 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 35 67 140 265 176 48 69 197 325), lower := (rows 35 67 140 265 176 48 64 128 256), losses := [] }

theorem u1236 : Upper (D 3) (R 3) [34,65,136,257,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1236
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1237 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 140 265 176 96 85 149 277), lower := (rows 35 67 140 265 176 96 64 128 256), losses := [] }

theorem u1237 : Upper (D 3) (R 3) [34,65,136,257,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1237
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1238 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 140 265 208 33 116 180 308), lower := (rows 35 67 140 265 208 33 64 128 256), losses := [] }

theorem u1238 : Upper (D 3) (R 3) [34,65,136,257,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1238
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1239 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 67 140 265 208 36 113 177 305), lower := (rows 35 67 140 265 208 36 64 128 256), losses := [] }

theorem u1239 : Upper (D 3) (R 3) [34,65,136,257,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1239
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1240 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 67 140 265 208 48 101 165 293), lower := (rows 35 67 140 265 208 48 64 128 256), losses := [] }

theorem u1240 : Upper (D 3) (R 3) [34,65,136,257,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1240
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1241 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 140 296 208 33 85 149 277), lower := (rows 35 67 140 296 208 33 64 128 256), losses := [] }

theorem u1241 : Upper (D 3) (R 3) [34,65,136,288,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1241
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1242 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 67 140 296 208 36 81 145 273), lower := (rows 35 67 140 296 208 36 64 128 256), losses := [] }

theorem u1242 : Upper (D 3) (R 3) [34,65,136,288,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1242
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1243 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 67 140 296 208 48 69 133 261), lower := (rows 35 67 140 296 208 48 64 128 256), losses := [] }

theorem u1243 : Upper (D 3) (R 3) [34,65,136,288,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1243
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1244 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 140 328 176 33 85 149 277), lower := (rows 35 67 140 328 176 33 64 128 256), losses := [] }

theorem u1244 : Upper (D 3) (R 3) [34,65,136,320,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1244
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1245 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 67 140 328 176 36 81 145 273), lower := (rows 35 67 140 328 176 36 64 128 256), losses := [] }

theorem u1245 : Upper (D 3) (R 3) [34,65,136,320,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1245
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1246 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 67 140 328 176 48 69 133 261), lower := (rows 35 67 140 328 176 48 64 128 256), losses := [] }

theorem u1246 : Upper (D 3) (R 3) [34,65,136,320,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1246
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1247 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 164 200 273 33 92 156 284), lower := (rows 35 67 164 200 273 33 64 128 256), losses := [] }

theorem u1247 : Upper (D 3) (R 3) [34,65,160,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1247
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1248 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 35 67 164 200 273 36 89 153 281), lower := (rows 35 67 164 200 273 36 64 128 256), losses := [] }

theorem u1248 : Upper (D 3) (R 3) [34,65,160,192,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1248
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1249 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 35 67 164 200 273 40 85 149 277), lower := (rows 35 67 164 200 273 40 64 128 256), losses := [] }

theorem u1249 : Upper (D 3) (R 3) [34,65,160,192,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1249
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1250 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 35 67 164 200 273 48 77 141 269), lower := (rows 35 67 164 200 273 48 64 128 256), losses := [] }

theorem u1250 : Upper (D 3) (R 3) [34,65,160,192,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1250
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1251 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 164 200 276 33 89 153 281), lower := (rows 35 67 164 200 276 33 64 128 256), losses := [] }

theorem u1251 : Upper (D 3) (R 3) [34,65,160,192,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1251
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1252 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 67 164 200 276 40 81 145 273), lower := (rows 35 67 164 200 276 40 64 128 256), losses := [] }

theorem u1252 : Upper (D 3) (R 3) [34,65,160,192,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1252
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1253 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 67 164 200 276 48 73 137 265), lower := (rows 35 67 164 200 276 48 64 128 256), losses := [] }

theorem u1253 : Upper (D 3) (R 3) [34,65,160,192,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1253
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1254 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 164 200 280 33 85 149 277), lower := (rows 35 67 164 200 280 33 64 128 256), losses := [] }

theorem u1254 : Upper (D 3) (R 3) [34,65,160,192,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1254
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1255 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 67 164 200 280 36 81 145 273), lower := (rows 35 67 164 200 280 36 64 128 256), losses := [] }

theorem u1255 : Upper (D 3) (R 3) [34,65,160,192,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1255
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1256 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 67 164 200 280 48 69 133 261), lower := (rows 35 67 164 200 280 48 64 128 256), losses := [] }

theorem u1256 : Upper (D 3) (R 3) [34,65,160,192,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1256
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1257 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 152 273 33 224 224 480), lower := (rows 35 70 13 152 273 33 64 128 256), losses := [] }

theorem u1257 : Upper (D 3) (R 3) [34,68,9,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1257
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1258 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 152 273 96 225 161 417), lower := (rows 35 70 13 152 273 96 64 128 256), losses := [] }

theorem u1258 : Upper (D 3) (R 3) [34,68,9,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1258
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1259 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 13 152 273 160 97 225 353), lower := (rows 35 70 13 152 273 160 64 128 256), losses := [] }

theorem u1259 : Upper (D 3) (R 3) [34,68,9,144,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1259
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1259
end Delivery.IrregularNine14.P03
