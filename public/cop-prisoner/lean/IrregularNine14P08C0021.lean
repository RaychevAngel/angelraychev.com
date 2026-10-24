import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0001
import IrregularNine14P08C0002

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1260 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 292 200 112 160 81 145 273), lower := (rows 7 42 292 200 112 160 64 128 256), losses := [] }

theorem u1260 : Upper (D 8) (R 8) [6,40,288,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1261 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 324 25 176 33 224 224 480), lower := (rows 7 42 324 25 176 33 64 128 256), losses := [] }

theorem u1261 : Upper (D 8) (R 8) [6,40,320,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1262 : Route 9 := (fun mask => (mask,id))

def c1262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1262 : Upper (D 8) (R 8) [6,40,320,17,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,160,64] 13 (by decide) (choices 1) [1,32,128] r1262 c1262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u112
  · exact u113
  · exact u114

def b1263 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 324 25 176 160 97 225 353), lower := (rows 7 42 324 25 176 160 64 128 256), losses := [] }

theorem u1263 : Upper (D 8) (R 8) [6,40,320,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1264 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 324 137 112 33 240 176 432), lower := (rows 7 42 324 137 112 33 64 128 256), losses := [] }

theorem u1264 : Upper (D 8) (R 8) [6,40,320,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1265 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 42 324 137 112 48 225 161 417), lower := (rows 7 42 324 137 112 48 64 128 256), losses := [] }

theorem u1265 : Upper (D 8) (R 8) [6,40,320,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1265 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1266 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 324 137 112 160 113 177 305), lower := (rows 7 42 324 137 112 160 64 128 256), losses := [] }

theorem u1266 : Upper (D 8) (R 8) [6,40,320,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1267 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 324 137 176 33 112 240 368), lower := (rows 7 42 324 137 176 33 64 128 256), losses := [] }

theorem u1267 : Upper (D 8) (R 8) [6,40,320,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1267 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1268 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 42 324 137 176 48 97 225 353), lower := (rows 7 42 324 137 176 48 64 128 256), losses := [] }

theorem u1268 : Upper (D 8) (R 8) [6,40,320,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1268 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1269 : Route 9 := (fun mask => (mask,id))

def c1269 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1269 : Upper (D 8) (R 8) [6,40,320,129,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,160,64] 13 (by decide) (choices 1) [1,16,32] r1269 c1269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u115
  · exact u116
  · exact u117

def b1270 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 324 137 208 33 112 176 304), lower := (rows 7 42 324 137 208 33 64 128 256), losses := [] }

theorem u1270 : Upper (D 8) (R 8) [6,40,320,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1270 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1271 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 42 324 137 208 48 97 161 289), lower := (rows 7 42 324 137 208 48 64 128 256), losses := [] }

theorem u1271 : Upper (D 8) (R 8) [6,40,320,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1271 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1272 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 324 152 49 33 224 224 480), lower := (rows 7 42 324 152 49 33 64 128 256), losses := [] }

theorem u1272 : Upper (D 8) (R 8) [6,40,320,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1273 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 138, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 152 49 96 225 161 417), lower := (rows 7 42 324 152 49 96 64 128 256), losses := [] }

theorem u1273 : Upper (D 8) (R 8) [6,40,320,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1273 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1274 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 324 152 49 160 97 225 353), lower := (rows 7 42 324 152 49 160 64 128 256), losses := [] }

theorem u1274 : Upper (D 8) (R 8) [6,40,320,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1275 : PairBound 9 := { available := 161, camps := [], pairs := [(1,6)], upper := (rows 7 42 324 152 112 33 225 161 417), lower := (rows 7 42 324 152 112 33 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 33 0 161 289), good := (rows 423 426 260 154 442 417 0 128 256) }] }

theorem u1275 : Upper (D 8) (R 8) [6,40,320,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1275 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1276 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 324 152 112 160 97 161 289), lower := (rows 7 42 324 152 112 160 64 128 256), losses := [] }

theorem u1276 : Upper (D 8) (R 8) [6,40,320,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1277 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 56 336 33 224 160 416), lower := (rows 7 67 140 56 336 33 64 128 256), losses := [] }

theorem u1277 : Upper (D 8) (R 8) [6,65,136,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1278 : Route 9 := (fun mask => (mask,id))

def c1278 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1278 : Upper (D 8) (R 8) [6,65,136,48,320,128] 13 := by
  apply FastRouting.sound _ _ [6,65,136,48,320,128] 13 (by decide) (choices 1) [1,32] r1278 c1278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u118
  · exact u119

def b1279 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 280 112 33 224 160 416), lower := (rows 7 67 140 280 112 33 64 128 256), losses := [] }

theorem u1279 : Upper (D 8) (R 8) [6,65,136,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1280 : Route 9 := (fun mask => (mask,id))

def c1280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1280 : Upper (D 8) (R 8) [6,65,136,272,96,128] 13 := by
  apply FastRouting.sound _ _ [6,65,136,272,96,128] 13 (by decide) (choices 1) [1,32] r1280 c1280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u120
  · exact u121

def b1281 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 296 112 33 240 176 432), lower := (rows 7 67 140 296 112 33 64 128 256), losses := [] }

theorem u1281 : Upper (D 8) (R 8) [6,65,136,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1281 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1282 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 67 140 296 112 48 225 161 417), lower := (rows 7 67 140 296 112 48 64 128 256), losses := [] }

theorem u1282 : Upper (D 8) (R 8) [6,65,136,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1282 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1283 : Route 9 := (fun mask => (mask,id))

def c1283 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1283 : Upper (D 8) (R 8) [6,65,136,288,96,128] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,96,128] 13 (by decide) (choices 1) [1,16,32] r1283 c1283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u122
  · exact u123
  · exact u124

def b1284 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 296 176 33 112 240 368), lower := (rows 7 67 140 296 176 33 64 128 256), losses := [] }

theorem u1284 : Upper (D 8) (R 8) [6,65,136,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1285 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 67 140 296 176 48 97 225 353), lower := (rows 7 67 140 296 176 48 64 128 256), losses := [] }

theorem u1285 : Upper (D 8) (R 8) [6,65,136,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1285 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1286 : Route 9 := (fun mask => (mask,id))

def c1286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1286 : Upper (D 8) (R 8) [6,65,136,288,160,64] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,160,64] 13 (by decide) (choices 1) [1,16,32] r1286 c1286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u125
  · exact u126
  · exact u127

def b1287 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 296 208 33 112 176 304), lower := (rows 7 67 140 296 208 33 64 128 256), losses := [] }

theorem u1287 : Upper (D 8) (R 8) [6,65,136,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1288 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 140 296 208 48 97 161 289), lower := (rows 7 67 140 296 208 48 64 128 256), losses := [] }

theorem u1288 : Upper (D 8) (R 8) [6,65,136,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1288 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1289 : PairBound 9 := { available := 296, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 56 208 33 360 424 296), lower := (rows 7 67 164 56 208 33 64 128 256), losses := [] }

theorem u1289 : Upper (D 8) (R 8) [6,65,160,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1290 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 7 67 164 56 208 40 353 417 289), lower := (rows 7 67 164 56 208 40 64 128 256), losses := [] }

theorem u1290 : Upper (D 8) (R 8) [6,65,160,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1290 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1291 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 67 164 56 208 288 105 169 297), lower := (rows 7 67 164 56 208 288 64 128 256), losses := [] }

theorem u1291 : Upper (D 8) (R 8) [6,65,160,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1291 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1292 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 56 280 33 224 224 480), lower := (rows 7 67 164 56 280 33 64 128 256), losses := [] }

theorem u1292 : Upper (D 8) (R 8) [6,65,160,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1293 : Route 9 := (fun mask => (mask,id))

def c1293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1293 : Upper (D 8) (R 8) [6,65,160,48,264,64] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,264,64] 13 (by decide) (choices 1) [1,32,128] r1293 c1293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u128
  · exact u129
  · exact u130

def b1294 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 164 56 280 160 97 225 353), lower := (rows 7 67 164 56 280 160 64 128 256), losses := [] }

theorem u1294 : Upper (D 8) (R 8) [6,65,160,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1295 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 56 336 33 232 168 424), lower := (rows 7 67 164 56 336 33 64 128 256), losses := [] }

theorem u1295 : Upper (D 8) (R 8) [6,65,160,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1296 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 67 164 56 336 40 225 161 417), lower := (rows 7 67 164 56 336 40 64 128 256), losses := [] }

theorem u1296 : Upper (D 8) (R 8) [6,65,160,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1296 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1297 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 164 56 336 160 105 169 297), lower := (rows 7 67 164 56 336 160 64 128 256), losses := [] }

theorem u1297 : Upper (D 8) (R 8) [6,65,160,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1297 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1298 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 56 400 33 104 232 360), lower := (rows 7 67 164 56 400 33 64 128 256), losses := [] }

theorem u1298 : Upper (D 8) (R 8) [6,65,160,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1299 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 67 164 56 400 40 97 225 353), lower := (rows 7 67 164 56 400 40 64 128 256), losses := [] }

theorem u1299 : Upper (D 8) (R 8) [6,65,160,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1299 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1300 : Route 9 := (fun mask => (mask,id))

def c1300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1300 : Upper (D 8) (R 8) [6,65,160,48,384,64] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,384,64] 13 (by decide) (choices 1) [1,8,32] r1300 c1300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u131
  · exact u132
  · exact u133

def b1301 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 88 304 33 232 168 424), lower := (rows 7 67 164 88 304 33 64 128 256), losses := [] }

theorem u1301 : Upper (D 8) (R 8) [6,65,160,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1301 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1302 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 67 164 88 304 40 225 161 417), lower := (rows 7 67 164 88 304 40 64 128 256), losses := [] }

theorem u1302 : Upper (D 8) (R 8) [6,65,160,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1302 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1303 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 164 88 304 160 105 169 297), lower := (rows 7 67 164 88 304 160 64 128 256), losses := [] }

theorem u1303 : Upper (D 8) (R 8) [6,65,160,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1303 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1304 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 88 400 33 104 168 296), lower := (rows 7 67 164 88 400 33 64 128 256), losses := [] }

theorem u1304 : Upper (D 8) (R 8) [6,65,160,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1305 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 164 88 400 40 97 161 289), lower := (rows 7 67 164 88 400 40 64 128 256), losses := [] }

theorem u1305 : Upper (D 8) (R 8) [6,65,160,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1305 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1306 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 104 152 33 368 432 304), lower := (rows 7 67 164 104 152 33 64 128 256), losses := [] }

theorem u1306 : Upper (D 8) (R 8) [6,65,160,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1306 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1307 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 7 67 164 104 152 48 353 417 289), lower := (rows 7 67 164 104 152 48 64 128 256), losses := [] }

theorem u1307 : Upper (D 8) (R 8) [6,65,160,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1307 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1308 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 67 164 104 152 288 113 177 305), lower := (rows 7 67 164 104 152 288 64 128 256), losses := [] }

theorem u1308 : Upper (D 8) (R 8) [6,65,160,96,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1308 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1309 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 104 280 33 240 176 432), lower := (rows 7 67 164 104 280 33 64 128 256), losses := [] }

theorem u1309 : Upper (D 8) (R 8) [6,65,160,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1310 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 67 164 104 280 48 225 161 417), lower := (rows 7 67 164 104 280 48 64 128 256), losses := [] }

theorem u1310 : Upper (D 8) (R 8) [6,65,160,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1310 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1311 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 164 104 280 160 113 177 305), lower := (rows 7 67 164 104 280 160 64 128 256), losses := [] }

theorem u1311 : Upper (D 8) (R 8) [6,65,160,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1311 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1312 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 104 304 33 216 152 408), lower := (rows 7 67 164 104 304 33 64 128 256), losses := [] }

theorem u1312 : Upper (D 8) (R 8) [6,65,160,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1313 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 67 164 104 304 40 209 145 401), lower := (rows 7 67 164 104 304 40 64 128 256), losses := [] }

theorem u1313 : Upper (D 8) (R 8) [6,65,160,96,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1313 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1314 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 7 67 164 104 304 48 201 137 393), lower := (rows 7 67 164 104 304 48 64 128 256), losses := [] }

theorem u1314 : Upper (D 8) (R 8) [6,65,160,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1314 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1315 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 164 104 304 160 89 153 281), lower := (rows 7 67 164 104 304 160 64 128 256), losses := [] }

theorem u1315 : Upper (D 8) (R 8) [6,65,160,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1316 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 104 400 33 120 184 312), lower := (rows 7 67 164 104 400 33 64 128 256), losses := [] }

theorem u1316 : Upper (D 8) (R 8) [6,65,160,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1317 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 67 164 104 400 40 113 177 305), lower := (rows 7 67 164 104 400 40 64 128 256), losses := [] }

theorem u1317 : Upper (D 8) (R 8) [6,65,160,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1317 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1318 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 67 164 104 400 48 105 169 297), lower := (rows 7 67 164 104 400 48 64 128 256), losses := [] }

theorem u1318 : Upper (D 8) (R 8) [6,65,160,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1318 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1319 : PairBound 9 := { available := 104, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 152 304 33 104 232 360), lower := (rows 7 67 164 152 304 33 64 128 256), losses := [] }

theorem u1319 : Upper (D 8) (R 8) [6,65,160,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1319
end Delivery.IrregularNine14.P08
