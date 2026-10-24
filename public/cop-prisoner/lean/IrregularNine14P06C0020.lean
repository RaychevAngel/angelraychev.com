import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1200 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 42 100 392 82 33 65 148 276), lower := (rows 7 42 100 392 82 33 65 128 256), losses := [] }

theorem u1200 : Upper (D 6) (R 6) [6,40,96,384,66,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1200
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1201 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(3,5),(4,5)], upper := (rows 7 42 100 392 82 33 68 145 273), lower := (rows 7 42 100 392 82 33 68 128 256), losses := [] }

theorem u1201 : Upper (D 6) (R 6) [6,40,96,384,66,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1201
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1202 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 392 82 33 80 133 261), lower := (rows 7 42 100 392 82 33 80 128 256), losses := [] }

theorem u1202 : Upper (D 6) (R 6) [6,40,96,384,66,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1202
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1203 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 133 26 336 33 68 224 352), lower := (rows 7 42 133 26 336 33 68 128 256), losses := [{ target := 0, region := (rows 0 34 4 42 48 32 69 160 288), good := (rows 78 442 196 26 336 506 68 128 256) }] }

theorem u1203 : Upper (D 6) (R 6) [6,40,129,18,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1203
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1204 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 133 26 336 33 96 196 324), lower := (rows 7 42 133 26 336 33 96 128 256), losses := [{ target := 0, region := (rows 0 98 4 123 49 32 98 129 257), good := (rows 478 122 412 90 346 506 122 128 256) }] }

theorem u1204 : Upper (D 6) (R 6) [6,40,129,18,320,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1204
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1205 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 133 26 336 36 65 224 352), lower := (rows 7 42 133 26 336 36 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 88 80 37 64 192 320), good := (rows 38 42 164 26 474 36 506 128 256) }] }

theorem u1205 : Upper (D 6) (R 6) [6,40,129,18,320,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1205
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1206 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 42 133 26 336 36 96 193 321), lower := (rows 7 42 133 26 336 36 96 128 256), losses := [{ target := 2, region := (rows 1 2 0 9 17 32 98 129 257), good := (rows 475 106 409 90 336 96 96 128 256) }] }

theorem u1206 : Upper (D 6) (R 6) [6,40,129,18,320,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1206
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1207 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 42 133 74 304 33 68 208 336), lower := (rows 7 42 133 74 304 33 68 128 256), losses := [] }

theorem u1207 : Upper (D 6) (R 6) [6,40,129,66,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1207
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1208 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 74, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 133 74 304 33 80 196 324), lower := (rows 7 42 133 74 304 33 80 128 256), losses := [] }

theorem u1208 : Upper (D 6) (R 6) [6,40,129,66,288,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1208
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1209 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 42 133 74 304 36 65 208 336), lower := (rows 7 42 133 74 304 36 65 128 256), losses := [] }

theorem u1209 : Upper (D 6) (R 6) [6,40,129,66,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1209
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1210 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 133 74 304 36 80 193 321), lower := (rows 7 42 133 74 304 36 80 128 256), losses := [] }

theorem u1210 : Upper (D 6) (R 6) [6,40,129,66,288,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1210
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1211 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 42 133 74 336 33 68 176 304), lower := (rows 7 42 133 74 336 33 68 128 256), losses := [] }

theorem u1211 : Upper (D 6) (R 6) [6,40,129,66,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1211
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1212 : PairBound 9 := { available := 36, camps := [{ cop := 8, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 42 133 74 336 33 80 164 292), lower := (rows 7 42 133 74 336 33 80 128 256), losses := [] }

theorem u1212 : Upper (D 6) (R 6) [6,40,129,66,320,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1212
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1213 : PairBound 9 := { available := 20, camps := [{ cop := 5, region := 74, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 74 336 33 96 148 276), lower := (rows 7 42 133 74 336 33 96 128 256), losses := [] }

theorem u1213 : Upper (D 6) (R 6) [6,40,129,66,320,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1213
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1214 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 42 133 74 336 36 65 176 304), lower := (rows 7 42 133 74 336 36 65 128 256), losses := [] }

theorem u1214 : Upper (D 6) (R 6) [6,40,129,66,320,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1214
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1215 : PairBound 9 := { available := 33, camps := [{ cop := 8, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 42 133 74 336 36 80 161 289), lower := (rows 7 42 133 74 336 36 80 128 256), losses := [] }

theorem u1215 : Upper (D 6) (R 6) [6,40,129,66,320,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1215
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1216 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 74, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 74 336 36 96 145 273), lower := (rows 7 42 133 74 336 36 96 128 256), losses := [] }

theorem u1216 : Upper (D 6) (R 6) [6,40,129,66,320,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1216
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1217 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 7 42 133 88 274 33 68 224 352), lower := (rows 7 42 133 88 274 33 68 128 256), losses := [{ target := 0, region := (rows 0 34 4 41 50 32 69 160 288), good := (rows 94 442 204 88 274 506 68 128 256) }] }

theorem u1217 : Upper (D 6) (R 6) [6,40,129,80,258,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1217
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1218 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 7 42 133 88 274 33 96 196 324), lower := (rows 7 42 133 88 274 33 96 128 256), losses := [{ target := 0, region := (rows 0 98 4 123 49 32 98 129 257), good := (rows 478 122 412 90 346 506 122 128 256) }] }

theorem u1218 : Upper (D 6) (R 6) [6,40,129,80,258,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1218
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1219 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 7 42 133 88 274 36 65 224 352), lower := (rows 7 42 133 88 274 36 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 72 88 37 64 192 320), good := (rows 38 58 164 474 274 36 506 128 256) }] }

theorem u1219 : Upper (D 6) (R 6) [6,40,129,80,258,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1219
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1220 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 7 42 133 88 274 36 96 193 321), lower := (rows 7 42 133 88 274 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 37 103 128 256), good := (rows 102 106 228 88 346 100 96 128 256) },{ target := 1, region := (rows 1 0 5 24 16 37 103 133 261), good := (rows 485 104 485 88 344 484 96 128 256) }] }

theorem u1220 : Upper (D 6) (R 6) [6,40,129,80,258,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1220
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1221 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 42 133 88 304 36 65 194 322), lower := (rows 7 42 133 88 304 36 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 72 82 37 64 200 328), good := (rows 54 442 164 474 304 36 506 128 256) }] }

theorem u1221 : Upper (D 6) (R 6) [6,40,129,80,288,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1221
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1222 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 88 304 36 66 193 321), lower := (rows 7 42 133 88 304 36 66 128 256), losses := [] }

theorem u1222 : Upper (D 6) (R 6) [6,40,129,80,288,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1222
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1223 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 98, targets := 5 },{ cop := 0, region := 112, targets := 1 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 42 133 265 52 96 66 208 336), lower := (rows 7 42 133 265 52 96 66 128 256), losses := [] }

theorem u1223 : Upper (D 6) (R 6) [6,40,129,257,36,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1223
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1224 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 42 133 265 52 96 80 194 322), lower := (rows 7 42 133 265 52 96 80 128 256), losses := [] }

theorem u1224 : Upper (D 6) (R 6) [6,40,129,257,36,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1224
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1225 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 7 42 133 265 82 96 68 176 304), lower := (rows 7 42 133 265 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 25 125 69 159 287), good := (rows 502 442 500 506 498 96 484 128 256) }] }

theorem u1225 : Upper (D 6) (R 6) [6,40,129,257,66,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1225
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1226 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 114, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 133 265 82 96 80 164 292), lower := (rows 7 42 133 265 82 96 80 128 256), losses := [] }

theorem u1226 : Upper (D 6) (R 6) [6,40,129,257,66,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1226
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1227 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 133, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 42 133 265 82 96 96 148 276), lower := (rows 7 42 133 265 82 96 96 128 256), losses := [] }

theorem u1227 : Upper (D 6) (R 6) [6,40,129,257,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1227
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1228 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 98, targets := 5 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 42 133 265 84 96 66 176 304), lower := (rows 7 42 133 265 84 96 66 128 256), losses := [] }

theorem u1228 : Upper (D 6) (R 6) [6,40,129,257,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1228
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1229 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 133 265 84 96 80 162 290), lower := (rows 7 42 133 265 84 96 80 128 256), losses := [] }

theorem u1229 : Upper (D 6) (R 6) [6,40,129,257,68,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1229
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1230 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 7 42 133 265 84 96 96 146 274), lower := (rows 7 42 133 265 84 96 96 128 256), losses := [] }

theorem u1230 : Upper (D 6) (R 6) [6,40,129,257,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1230
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1231 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 42 133 266 52 96 65 208 336), lower := (rows 7 42 133 266 52 96 65 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 117 69 144 272), good := (rows 99 42 225 266 506 96 97 128 256) }] }

theorem u1231 : Upper (D 6) (R 6) [6,40,129,258,36,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1231
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1232 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 42 133 266 52 96 80 193 321), lower := (rows 7 42 133 266 52 96 80 128 256), losses := [] }

theorem u1232 : Upper (D 6) (R 6) [6,40,129,258,36,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1232
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1233 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 298, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 266 81 96 68 176 304), lower := (rows 7 42 133 266 81 96 68 128 256), losses := [] }

theorem u1233 : Upper (D 6) (R 6) [6,40,129,258,65,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1233
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1234 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 133 266 81 96 80 164 292), lower := (rows 7 42 133 266 81 96 80 128 256), losses := [] }

theorem u1234 : Upper (D 6) (R 6) [6,40,129,258,65,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1234
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1235 : PairBound 9 := { available := 20, camps := [{ cop := 8, region := 106, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 266 81 96 96 148 276), lower := (rows 7 42 133 266 81 96 96 128 256), losses := [] }

theorem u1235 : Upper (D 6) (R 6) [6,40,129,258,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1235
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1236 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 298, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 266 84 96 65 176 304), lower := (rows 7 42 133 266 84 96 65 128 256), losses := [] }

theorem u1236 : Upper (D 6) (R 6) [6,40,129,258,68,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1236
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1237 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 133 266 84 96 80 161 289), lower := (rows 7 42 133 266 84 96 80 128 256), losses := [] }

theorem u1237 : Upper (D 6) (R 6) [6,40,129,258,68,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1237
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1238 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 106, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 266 84 96 96 145 273), lower := (rows 7 42 133 266 84 96 96 128 256), losses := [] }

theorem u1238 : Upper (D 6) (R 6) [6,40,129,258,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1238
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1239 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 266, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 266 112 33 68 208 336), lower := (rows 7 42 133 266 112 33 68 128 256), losses := [] }

theorem u1239 : Upper (D 6) (R 6) [6,40,129,258,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1239
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1240 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 244, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 42 133 266 112 33 80 196 324), lower := (rows 7 42 133 266 112 33 80 128 256), losses := [] }

theorem u1240 : Upper (D 6) (R 6) [6,40,129,258,96,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1240
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1241 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 266, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 266 112 36 65 208 336), lower := (rows 7 42 133 266 112 36 65 128 256), losses := [] }

theorem u1241 : Upper (D 6) (R 6) [6,40,129,258,96,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1241
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1242 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 42 133 266 112 36 80 193 321), lower := (rows 7 42 133 266 112 36 80 128 256), losses := [] }

theorem u1242 : Upper (D 6) (R 6) [6,40,129,258,96,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1242
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1243 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 98, targets := 5 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 7 42 133 268 49 96 66 208 336), lower := (rows 7 42 133 268 49 96 66 128 256), losses := [] }

theorem u1243 : Upper (D 6) (R 6) [6,40,129,260,33,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1243
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1244 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 112, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(4,1),(4,2)], upper := (rows 7 42 133 268 49 96 80 194 322), lower := (rows 7 42 133 268 49 96 80 128 256), losses := [] }

theorem u1244 : Upper (D 6) (R 6) [6,40,129,260,33,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1244
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1245 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 98, targets := 5 },{ cop := 4, region := 164, targets := 2 }], pairs := [(1,0),(1,2),(2,1)], upper := (rows 7 42 133 268 81 96 66 176 304), lower := (rows 7 42 133 268 81 96 66 128 256), losses := [] }

theorem u1245 : Upper (D 6) (R 6) [6,40,129,260,65,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1245
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1246 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 133 268 81 96 80 162 290), lower := (rows 7 42 133 268 81 96 80 128 256), losses := [] }

theorem u1246 : Upper (D 6) (R 6) [6,40,129,260,65,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1246
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1247 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 98, targets := 5 },{ cop := 0, region := 112, targets := 2 }], pairs := [(1,0),(1,2),(4,1)], upper := (rows 7 42 133 268 81 96 96 146 274), lower := (rows 7 42 133 268 81 96 96 128 256), losses := [] }

theorem u1247 : Upper (D 6) (R 6) [6,40,129,260,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1247
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1248 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 7 42 133 268 82 96 65 176 304), lower := (rows 7 42 133 268 82 96 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 9 112 112 64 242 370), good := (rows 398 442 140 268 498 498 506 128 256) }] }

theorem u1248 : Upper (D 6) (R 6) [6,40,129,260,66,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1248
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1249 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 114, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 133 268 82 96 80 161 289), lower := (rows 7 42 133 268 82 96 80 128 256), losses := [] }

theorem u1249 : Upper (D 6) (R 6) [6,40,129,260,66,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1249
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1250 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 133, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 42 133 268 82 96 96 145 273), lower := (rows 7 42 133 268 82 96 96 128 256), losses := [] }

theorem u1250 : Upper (D 6) (R 6) [6,40,129,260,66,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1250
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1251 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 0, region := 112, targets := 2 }], pairs := [(0,5),(2,5),(4,1)], upper := (rows 7 42 133 280 52 96 65 194 322), lower := (rows 7 42 133 280 52 96 65 128 256), losses := [] }

theorem u1251 : Upper (D 6) (R 6) [6,40,129,272,36,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1251
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1252 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 42 133 280 52 96 66 193 321), lower := (rows 7 42 133 280 52 96 66 128 256), losses := [] }

theorem u1252 : Upper (D 6) (R 6) [6,40,129,272,36,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1252
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1253 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,0),(4,5)], upper := (rows 7 42 133 280 82 33 68 224 352), lower := (rows 7 42 133 280 82 33 68 128 256), losses := [] }

theorem u1253 : Upper (D 6) (R 6) [6,40,129,272,66,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1253
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1254 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 133 280 82 33 96 196 324), lower := (rows 7 42 133 280 82 33 96 128 256), losses := [] }

theorem u1254 : Upper (D 6) (R 6) [6,40,129,272,66,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1254
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1255 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 7 42 133 280 82 36 65 224 352), lower := (rows 7 42 133 280 82 36 65 128 256), losses := [] }

theorem u1255 : Upper (D 6) (R 6) [6,40,129,272,66,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1255
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1256 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 133 280 82 36 96 193 321), lower := (rows 7 42 133 280 82 36 96 128 256), losses := [] }

theorem u1256 : Upper (D 6) (R 6) [6,40,129,272,66,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1256
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1257 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 266, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 133 280 112 36 65 194 322), lower := (rows 7 42 133 280 112 36 65 128 256), losses := [] }

theorem u1257 : Upper (D 6) (R 6) [6,40,129,272,96,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1257
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1258 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,2)], upper := (rows 7 42 133 280 112 36 66 193 321), lower := (rows 7 42 133 280 112 36 66 128 256), losses := [] }

theorem u1258 : Upper (D 6) (R 6) [6,40,129,272,96,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1258
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1259 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 164, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 7 42 133 328 81 36 66 176 304), lower := (rows 7 42 133 328 81 36 66 128 256), losses := [] }

theorem u1259 : Upper (D 6) (R 6) [6,40,129,320,65,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1259
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1259
end Delivery.IrregularNine14.P06
