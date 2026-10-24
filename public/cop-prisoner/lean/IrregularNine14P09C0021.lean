import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0000

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1260 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 5, region := 80, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 13 152 112 288 320 129 385), lower := (rows 35 70 13 152 112 288 320 128 256), losses := [] }

theorem u1260 : Upper (D 9) (R 9) [34,68,9,144,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1260 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1261 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 336, targets := 128 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8),(4,7)], upper := (rows 35 70 13 152 273 160 96 448 320), lower := (rows 35 70 13 152 273 160 96 128 256), losses := [] }

theorem u1261 : Upper (D 9) (R 9) [34,68,9,144,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1261 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1262 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 336, targets := 128 },{ cop := 1, region := 161, targets := 256 },{ cop := 2, region := 482, targets := 1 },{ cop := 4, region := 232, targets := 1 }], pairs := [(0,8),(1,0),(1,7),(3,0),(4,7)], upper := (rows 35 70 13 152 273 160 320 224 352), lower := (rows 35 70 13 152 273 160 320 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 21 32 373 0 289), good := (rows 371 86 351 88 337 352 320 0 320) }] }

theorem u1262 : Upper (D 9) (R 9) [34,68,9,144,257,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1262 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1263 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 1, region := 440, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,0)], upper := (rows 35 70 13 152 304 160 65 448 320), lower := (rows 35 70 13 152 304 160 65 128 256), losses := [] }

theorem u1263 : Upper (D 9) (R 9) [34,68,9,144,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1263 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1264 : Route 9 := (fun mask => (mask,id))

def c1264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1264 : Upper (D 9) (R 9) [34,68,9,144,288,128,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,288,128,256] 13 (by decide) (choices 1) [1,64] r1264 c1264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u52
  · exact u53

def b1265 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0),(4,0)], upper := (rows 35 70 13 152 336 160 65 416 288), lower := (rows 35 70 13 152 336 160 65 128 256), losses := [] }

theorem u1265 : Upper (D 9) (R 9) [34,68,9,144,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1265 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1266 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 336, targets := 128 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(4,7)], upper := (rows 35 70 13 152 336 160 96 385 257), lower := (rows 35 70 13 152 336 160 96 128 256), losses := [] }

theorem u1266 : Upper (D 9) (R 9) [34,68,9,144,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1266 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1267 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 70 13 152 336 160 320 161 289), lower := (rows 35 70 13 152 336 160 320 128 256), losses := [] }

theorem u1267 : Upper (D 9) (R 9) [34,68,9,144,320,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1267 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1268 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0),(4,0)], upper := (rows 35 70 13 152 336 288 65 160 416), lower := (rows 35 70 13 152 336 288 65 128 256), losses := [] }

theorem u1268 : Upper (D 9) (R 9) [34,68,9,144,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1268 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1269 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 80, targets := 129 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,0),(2,5),(4,0),(4,7)], upper := (rows 35 70 13 152 336 288 96 129 385), lower := (rows 35 70 13 152 336 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 304 304 377 128 256), good := (rows 114 70 78 248 368 368 112 128 368) },{ target := 5, region := (rows 1 2 5 11 18 0 64 133 261), good := (rows 415 478 397 152 336 256 64 128 256) }] }

theorem u1269 : Upper (D 9) (R 9) [34,68,9,144,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1269 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1270 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 305, targets := 128 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,5),(4,7)], upper := (rows 35 70 13 152 336 288 192 161 289), lower := (rows 35 70 13 152 336 288 192 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 304 200 128 256), good := (rows 34 70 78 248 368 288 192 192 288) },{ target := 5, region := (rows 1 6 4 8 16 0 200 128 256), good := (rows 3 70 79 216 336 256 192 192 256) }] }

theorem u1270 : Upper (D 9) (R 9) [34,68,9,144,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1270 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1271 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 13 168 145 288 80 448 320), lower := (rows 35 70 13 168 145 288 80 128 256), losses := [] }

theorem u1271 : Upper (D 9) (R 9) [34,68,9,160,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1271 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1272 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 360, targets := 1 }], pairs := [(0,6),(0,7),(1,5),(3,0),(4,5)], upper := (rows 35 70 13 168 145 288 320 208 336), lower := (rows 35 70 13 168 145 288 320 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 352 0 128 256), good := (rows 35 39 13 168 145 288 288 128 288) },{ target := 7, region := (rows 11 10 12 8 16 368 368 0 272), good := (rows 99 103 15 111 369 352 352 0 352) }] }

theorem u1272 : Upper (D 9) (R 9) [34,68,9,160,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1272 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1273 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 87, targets := 256 },{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 13 168 208 288 65 400 272), lower := (rows 35 70 13 168 208 288 65 128 256), losses := [] }

theorem u1273 : Upper (D 9) (R 9) [34,68,9,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1273 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1274 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 13 168 208 288 80 385 257), lower := (rows 35 70 13 168 208 288 80 128 256), losses := [] }

theorem u1274 : Upper (D 9) (R 9) [34,68,9,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1274 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1275 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(0,6),(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 70 13 168 208 288 320 145 273), lower := (rows 35 70 13 168 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 24 352 352 128 256), good := (rows 98 102 28 248 248 352 352 128 352) },{ target := 6, region := (rows 3 2 4 24 16 352 0 128 256), good := (rows 35 39 13 168 184 288 288 128 288) }] }

theorem u1275 : Upper (D 9) (R 9) [34,68,9,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1275 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1276 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 1, region := 424, targets := 1 }], pairs := [(1,5),(1,8),(3,0),(4,5)], upper := (rows 35 70 13 168 273 288 80 192 448), lower := (rows 35 70 13 168 273 288 80 128 256), losses := [{ target := 8, region := (rows 1 82 21 9 16 32 80 210 0), good := (rows 175 198 13 168 223 32 214 128 0) }] }

theorem u1276 : Upper (D 9) (R 9) [34,68,9,160,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1276 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1277 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 1, region := 305, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,7)], upper := (rows 35 70 13 168 273 288 192 208 336), lower := (rows 35 70 13 168 273 288 192 128 256), losses := [] }

theorem u1277 : Upper (D 9) (R 9) [34,68,9,160,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1277 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1278 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 70 13 168 336 288 65 144 400), lower := (rows 35 70 13 168 336 288 65 128 256), losses := [] }

theorem u1278 : Upper (D 9) (R 9) [34,68,9,160,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1278 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1279 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 0, region := 140, targets := 256 }], pairs := [(0,6),(2,6),(2,8),(3,6)], upper := (rows 35 70 13 168 336 288 80 129 385), lower := (rows 35 70 13 168 336 288 80 128 256), losses := [] }

theorem u1279 : Upper (D 9) (R 9) [34,68,9,160,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1279 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1280 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 1, region := 305, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,7)], upper := (rows 35 70 13 168 336 288 192 145 273), lower := (rows 35 70 13 168 336 288 192 128 256), losses := [] }

theorem u1280 : Upper (D 9) (R 9) [34,68,9,160,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1280 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1281 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 70 13 168 400 288 65 208 336), lower := (rows 35 70 13 168 400 288 65 128 256), losses := [] }

theorem u1281 : Upper (D 9) (R 9) [34,68,9,160,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1281 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1282 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 1, region := 289, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,5),(3,0),(4,5)], upper := (rows 35 70 13 168 400 288 80 193 321), lower := (rows 35 70 13 168 400 288 80 128 256), losses := [] }

theorem u1282 : Upper (D 9) (R 9) [34,68,9,160,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1282 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1283 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 78, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 70 13 200 145 288 80 416 288), lower := (rows 35 70 13 200 145 288 80 128 256), losses := [] }

theorem u1283 : Upper (D 9) (R 9) [34,68,9,192,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1283 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1284 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 },{ cop := 4, region := 360, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,5),(4,6)], upper := (rows 35 70 13 200 145 288 96 400 272), lower := (rows 35 70 13 200 145 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 304 369 144 272), good := (rows 98 70 78 200 504 352 96 128 352) }] }

theorem u1284 : Upper (D 9) (R 9) [34,68,9,192,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1284 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1285 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 },{ cop := 4, region := 360, targets := 1 }], pairs := [(0,6),(0,7),(3,0),(4,6),(4,8)], upper := (rows 35 70 13 200 145 288 320 176 304), lower := (rows 35 70 13 200 145 288 320 128 256), losses := [{ target := 7, region := (rows 11 10 12 8 16 368 368 0 272), good := (rows 99 103 15 111 369 352 352 0 352) }] }

theorem u1285 : Upper (D 9) (R 9) [34,68,9,192,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1285 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1286 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 1, region := 440, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 35 70 13 200 176 288 65 400 272), lower := (rows 35 70 13 200 176 288 65 128 256), losses := [] }

theorem u1286 : Upper (D 9) (R 9) [34,68,9,192,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1286 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1287 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 13 200 176 288 80 385 257), lower := (rows 35 70 13 200 176 288 80 128 256), losses := [] }

theorem u1287 : Upper (D 9) (R 9) [34,68,9,192,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1287 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1288 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 }], pairs := [(0,6),(3,0),(4,0),(4,6),(4,8)], upper := (rows 35 70 13 200 176 288 320 145 273), lower := (rows 35 70 13 200 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 24 352 352 128 256), good := (rows 98 102 28 248 248 352 352 128 352) }] }

theorem u1288 : Upper (D 9) (R 9) [34,68,9,192,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1288 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1289 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 424, targets := 1 }], pairs := [(0,6),(1,8),(3,0),(4,6)], upper := (rows 35 70 13 200 273 288 80 160 416), lower := (rows 35 70 13 200 273 288 80 128 256), losses := [{ target := 8, region := (rows 1 82 20 24 16 32 80 161 0), good := (rows 163 70 141 202 223 160 94 128 0) }] }

theorem u1289 : Upper (D 9) (R 9) [34,68,9,192,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1289 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1290 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 },{ cop := 4, region := 232, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,5),(4,6)], upper := (rows 35 70 13 200 273 288 96 144 400), lower := (rows 35 70 13 200 273 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 304 369 144 272), good := (rows 98 70 78 200 504 352 96 128 352) }] }

theorem u1290 : Upper (D 9) (R 9) [34,68,9,192,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1290 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1291 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 70 13 200 273 288 192 176 304), lower := (rows 35 70 13 200 273 288 192 128 256), losses := [] }

theorem u1291 : Upper (D 9) (R 9) [34,68,9,192,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1291 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1292 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 13 200 400 48 65 416 288), lower := (rows 35 70 13 200 400 48 65 128 256), losses := [] }

theorem u1292 : Upper (D 9) (R 9) [34,68,9,192,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1292 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1293 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 13 200 400 48 96 385 257), lower := (rows 35 70 13 200 400 48 96 128 256), losses := [] }

theorem u1293 : Upper (D 9) (R 9) [34,68,9,192,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1293 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1294 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 72, targets := 1 },{ cop := 4, region := 72, targets := 32 }], pairs := [(0,6),(3,0),(3,5),(4,6)], upper := (rows 35 70 13 200 400 48 320 161 289), lower := (rows 35 70 13 200 400 48 320 128 256), losses := [] }

theorem u1294 : Upper (D 9) (R 9) [34,68,9,192,384,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1294 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1295 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0),(4,0)], upper := (rows 35 70 13 200 400 288 65 176 304), lower := (rows 35 70 13 200 400 288 65 128 256), losses := [] }

theorem u1295 : Upper (D 9) (R 9) [34,68,9,192,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1295 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1296 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 35 70 13 200 400 288 80 161 289), lower := (rows 35 70 13 200 400 288 80 128 256), losses := [] }

theorem u1296 : Upper (D 9) (R 9) [34,68,9,192,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1296 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1297 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 },{ cop := 4, region := 104, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,5),(4,6)], upper := (rows 35 70 13 200 400 288 96 145 273), lower := (rows 35 70 13 200 400 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 304 369 128 256), good := (rows 98 70 78 200 504 352 96 128 352) }] }

theorem u1297 : Upper (D 9) (R 9) [34,68,9,192,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1297 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1298 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 119, targets := 256 },{ cop := 1, region := 440, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 35 70 13 392 112 160 65 400 272), lower := (rows 35 70 13 392 112 160 65 128 256), losses := [] }

theorem u1298 : Upper (D 9) (R 9) [34,68,9,384,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1298 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1299 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 13 392 112 160 80 385 257), lower := (rows 35 70 13 392 112 160 80 128 256), losses := [] }

theorem u1299 : Upper (D 9) (R 9) [34,68,9,384,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1299 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1300 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 177, targets := 256 },{ cop := 0, region := 336, targets := 128 },{ cop := 3, region := 112, targets := 1 }], pairs := [(0,8),(1,0),(4,0),(4,7),(4,8)], upper := (rows 35 70 13 392 112 160 320 145 273), lower := (rows 35 70 13 392 112 160 320 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 28 168 328 128 256), good := (rows 34 86 126 504 112 160 320 160 320) }] }

theorem u1300 : Upper (D 9) (R 9) [34,68,9,384,96,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1300 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1301 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 13 392 145 48 96 448 320), lower := (rows 35 70 13 392 145 48 96 128 256), losses := [] }

theorem u1301 : Upper (D 9) (R 9) [34,68,9,384,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1301 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1302 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 177, targets := 256 },{ cop := 0, region := 456, targets := 1 }], pairs := [(0,8),(1,0),(3,0),(4,8)], upper := (rows 35 70 13 392 145 48 320 224 352), lower := (rows 35 70 13 392 145 48 320 128 256), losses := [{ target := 0, region := (rows 0 6 4 61 16 48 381 177 305), good := (rows 490 78 462 456 504 504 320 128 320) }] }

theorem u1302 : Upper (D 9) (R 9) [34,68,9,384,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1302 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1303 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 208, targets := 256 },{ cop := 1, region := 424, targets := 1 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,7),(1,8),(3,0),(4,8)], upper := (rows 35 70 13 392 145 288 80 224 352), lower := (rows 35 70 13 392 145 288 80 128 256), losses := [{ target := 8, region := (rows 1 6 4 8 21 32 87 129 0), good := (rows 243 86 223 136 209 32 80 128 0) }] }

theorem u1303 : Upper (D 9) (R 9) [34,68,9,384,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1303 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1304 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 208, targets := 256 },{ cop := 4, region := 360, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,8)], upper := (rows 35 70 13 392 145 288 96 208 336), lower := (rows 35 70 13 392 145 288 96 128 256), losses := [] }

theorem u1304 : Upper (D 9) (R 9) [34,68,9,384,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1304 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1305 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0),(4,0)], upper := (rows 35 70 13 392 176 288 65 208 336), lower := (rows 35 70 13 392 176 288 65 128 256), losses := [] }

theorem u1305 : Upper (D 9) (R 9) [34,68,9,384,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1305 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1306 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 208, targets := 256 },{ cop := 1, region := 289, targets := 128 },{ cop := 3, region := 48, targets := 1 },{ cop := 3, region := 48, targets := 64 }], pairs := [(0,7),(4,0),(4,6),(4,8)], upper := (rows 35 70 13 392 176 288 80 193 321), lower := (rows 35 70 13 392 176 288 80 128 256), losses := [] }

theorem u1306 : Upper (D 9) (R 9) [34,68,9,384,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1306 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1307 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 13 392 208 48 65 416 288), lower := (rows 35 70 13 392 208 48 65 128 256), losses := [] }

theorem u1307 : Upper (D 9) (R 9) [34,68,9,384,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1307 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1308 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 396, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6)], upper := (rows 35 70 13 392 208 48 96 385 257), lower := (rows 35 70 13 392 208 48 96 128 256), losses := [] }

theorem u1308 : Upper (D 9) (R 9) [34,68,9,384,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1308 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1309 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 177, targets := 256 }], pairs := [(0,8),(2,6),(3,6),(4,8)], upper := (rows 35 70 13 392 208 48 320 161 289), lower := (rows 35 70 13 392 208 48 320 128 256), losses := [] }

theorem u1309 : Upper (D 9) (R 9) [34,68,9,384,192,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1309 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1310 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0),(4,0)], upper := (rows 35 70 13 392 208 288 65 176 304), lower := (rows 35 70 13 392 208 288 65 128 256), losses := [] }

theorem u1310 : Upper (D 9) (R 9) [34,68,9,384,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1310 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1311 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 7, region := 80, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 35 70 13 392 208 288 80 161 289), lower := (rows 35 70 13 392 208 288 80 128 256), losses := [] }

theorem u1311 : Upper (D 9) (R 9) [34,68,9,384,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1311 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1312 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 208, targets := 256 },{ cop := 3, region := 112, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(4,0),(4,8)], upper := (rows 35 70 13 392 208 288 96 145 273), lower := (rows 35 70 13 392 208 288 96 128 256), losses := [] }

theorem u1312 : Upper (D 9) (R 9) [34,68,9,384,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1312 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1313 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 70 28 73 145 288 96 384 384), lower := (rows 35 70 28 73 145 288 96 128 256), losses := [] }

theorem u1313 : Upper (D 9) (R 9) [34,68,24,65,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1313 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1314 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 78, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8),(3,5)], upper := (rows 35 70 28 73 145 288 192 416 288), lower := (rows 35 70 28 73 145 288 192 128 256), losses := [] }

theorem u1314 : Upper (D 9) (R 9) [34,68,24,65,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1314 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1315 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 },{ cop := 2, region := 482, targets := 1 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,6),(4,8)], upper := (rows 35 70 28 73 145 288 320 160 416), lower := (rows 35 70 28 73 145 288 320 128 256), losses := [] }

theorem u1315 : Upper (D 9) (R 9) [34,68,24,65,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1315 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1316 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 3, region := 438, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8),(3,8)], upper := (rows 35 70 28 73 400 160 65 416 288), lower := (rows 35 70 28 73 400 160 65 128 256), losses := [] }

theorem u1316 : Upper (D 9) (R 9) [34,68,24,65,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1316 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1317 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 3, region := 406, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8),(3,8)], upper := (rows 35 70 28 73 400 160 96 385 257), lower := (rows 35 70 28 73 400 160 96 128 256), losses := [] }

theorem u1317 : Upper (D 9) (R 9) [34,68,24,65,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1317 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1318 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 169, targets := 256 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(0,8),(3,7),(3,8),(4,6)], upper := (rows 35 70 28 73 400 160 320 161 289), lower := (rows 35 70 28 73 400 160 320 128 256), losses := [] }

theorem u1318 : Upper (D 9) (R 9) [34,68,24,65,384,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1318 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1319 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 72, targets := 384 },{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(3,7),(3,8),(4,5),(4,6)], upper := (rows 35 70 28 104 145 288 65 384 384), lower := (rows 35 70 28 104 145 288 65 128 256), losses := [] }

theorem u1319 : Upper (D 9) (R 9) [34,68,24,96,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1319 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1319
end Delivery.IrregularNine14.P09
