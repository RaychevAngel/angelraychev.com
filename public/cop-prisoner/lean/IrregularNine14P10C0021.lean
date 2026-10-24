import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0006

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1260 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 16, targets := 288 }], pairs := [(4,5),(4,8)], upper := (rows 7 35 196 56 208 296 360 424 296), lower := (rows 7 35 196 56 208 32 64 128 256), losses := [] }

theorem u1260 : Upper (D 10) (R 10) [6,33,192,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1260 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1261 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1261 : Upper (D 10) (R 10) [6,33,192,48,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,264] 13 (by decide) (choices 1) [64,256] r1261 c1261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u381
  · exact u382

def b1262 : PairBound 9 := { available := 456, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 35 196 56 304 488 456 456 456), lower := (rows 7 35 196 56 304 32 64 128 256), losses := [] }

theorem u1262 : Upper (D 10) (R 10) [6,33,192,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1262 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1263 : Route 9 := (fun mask => (mask,id))

def c1263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1263 : Upper (D 10) (R 10) [6,33,192,48,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,320] 13 (by decide) (choices 1) [8,128,256] r1263 c1263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u383
  · exact u384
  · exact u385

def b1264 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 24, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 35 196 88 152 288 352 416 288), lower := (rows 7 35 196 88 152 32 64 128 256), losses := [] }

theorem u1264 : Upper (D 10) (R 10) [6,33,192,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1264 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1265 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 432, targets := 64 },{ cop := 4, region := 328, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 7 35 196 88 176 296 360 424 296), lower := (rows 7 35 196 88 176 32 64 128 256), losses := [] }

theorem u1265 : Upper (D 10) (R 10) [6,33,192,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1265 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1266 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 88 280 416 480 416 416), lower := (rows 7 35 196 88 280 32 64 128 256), losses := [] }

theorem u1266 : Upper (D 10) (R 10) [6,33,192,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1266 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1267 : Route 9 := (fun mask => (mask,id))

def c1267 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1267 : Upper (D 10) (R 10) [6,33,192,80,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,288] 13 (by decide) (choices 1) [8,128,256] r1267 c1267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u386
  · exact u387
  · exact u388

def b1268 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 432, targets := 64 },{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 7 35 196 88 400 296 360 424 296), lower := (rows 7 35 196 88 400 32 64 128 256), losses := [] }

theorem u1268 : Upper (D 10) (R 10) [6,33,192,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1268 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1269 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 400, targets := 64 },{ cop := 4, region := 328, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 7 35 196 104 176 312 344 408 280), lower := (rows 7 35 196 104 176 32 64 128 256), losses := [] }

theorem u1269 : Upper (D 10) (R 10) [6,33,192,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1269 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1270 : Route 9 := (fun mask => (mask,id))

def c1270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1270 : Upper (D 10) (R 10) [6,33,192,96,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,264] 13 (by decide) (choices 1) [16,128,256] r1270 c1270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u389
  · exact u390
  · exact u391

def r1271 : Route 9 := (fun mask => (mask,id))

def c1271 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u1271 : Upper (D 10) (R 10) [6,33,192,96,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,288] 13 (by decide) (choices 1) [8,16,128,256] r1271 c1271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u392
  · exact u393
  · exact u394
  · exact u395

def b1272 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 400, targets := 64 },{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 7 35 196 104 400 312 376 440 312), lower := (rows 7 35 196 104 400 32 64 128 256), losses := [] }

theorem u1272 : Upper (D 10) (R 10) [6,33,192,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1272 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1273 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 35 196 200 280 304 368 432 304), lower := (rows 7 35 196 200 280 32 64 128 256), losses := [] }

theorem u1273 : Upper (D 10) (R 10) [6,33,192,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1273 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1274 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 35 196 200 304 312 376 440 312), lower := (rows 7 35 196 200 304 32 64 128 256), losses := [] }

theorem u1274 : Upper (D 10) (R 10) [6,33,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1274 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1275 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 24, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 35 196 280 280 224 224 224 480), lower := (rows 7 35 196 280 280 32 64 128 256), losses := [] }

theorem u1275 : Upper (D 10) (R 10) [6,33,192,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1275 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1276 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 35 196 280 304 232 232 232 488), lower := (rows 7 35 196 280 304 32 64 128 256), losses := [] }

theorem u1276 : Upper (D 10) (R 10) [6,33,192,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1276 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1277 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 35 196 280 336 168 232 168 424), lower := (rows 7 35 196 280 336 32 64 128 256), losses := [] }

theorem u1277 : Upper (D 10) (R 10) [6,33,192,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1277 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1278 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 7 35 196 296 304 248 216 216 472), lower := (rows 7 35 196 296 304 32 64 128 256), losses := [] }

theorem u1278 : Upper (D 10) (R 10) [6,33,192,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1278 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1279 : Route 9 := (fun mask => (mask,id))

def c1279 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1279 : Upper (D 10) (R 10) [6,33,192,288,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,288,320] 13 (by decide) (choices 1) [8,16,128] r1279 c1279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u396
  · exact u397
  · exact u398

def b1280 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 176, targets := 64 },{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 7 35 196 328 400 56 120 184 312), lower := (rows 7 35 196 328 400 32 64 128 256), losses := [] }

theorem u1280 : Upper (D 10) (R 10) [6,33,192,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1280 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1281 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 11, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 42 52 41 208 480 448 448 448), lower := (rows 7 42 52 41 208 32 64 128 256), losses := [] }

theorem u1281 : Upper (D 10) (R 10) [6,40,48,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1281 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1282 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 15, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 52 73 112 416 448 384 384), lower := (rows 7 42 52 73 112 32 64 128 256), losses := [] }

theorem u1282 : Upper (D 10) (R 10) [6,40,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1282 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1283 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 7 42 52 73 176 480 448 448 448), lower := (rows 7 42 52 73 176 32 64 128 256), losses := [] }

theorem u1283 : Upper (D 10) (R 10) [6,40,48,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1283 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1284 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 418, targets := 64 },{ cop := 4, region := 292, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 7 42 52 73 208 416 480 416 416), lower := (rows 7 42 52 73 208 32 64 128 256), losses := [] }

theorem u1284 : Upper (D 10) (R 10) [6,40,48,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1284 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1285 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1285 : Upper (D 10) (R 10) [6,40,48,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,384] 13 (by decide) (choices 1) [64,128] r1285 c1285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u399
  · exact u400

def b1286 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 52 104 208 417 449 385 385), lower := (rows 7 42 52 104 208 32 64 128 256), losses := [] }

theorem u1286 : Upper (D 10) (R 10) [6,40,48,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1286 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1287 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 52 104 400 481 449 449 449), lower := (rows 7 42 52 104 400 32 64 128 256), losses := [] }

theorem u1287 : Upper (D 10) (R 10) [6,40,48,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1287 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1288 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 16, targets := 288 }], pairs := [(4,5),(4,8)], upper := (rows 7 42 52 200 208 289 353 417 289), lower := (rows 7 42 52 200 208 32 64 128 256), losses := [] }

theorem u1288 : Upper (D 10) (R 10) [6,40,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1288 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m1289_256 : Upper (D 10) (R 10) [6,40,48,192,320,256] 13 :=
  permutation_upper _ _ _ [6,40,48,192,320,128] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u402

def r1289 : Route 9 := (fun mask => (mask,id))

def c1289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1289 : Upper (D 10) (R 10) [6,40,48,192,320] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,320] 13 (by decide) (choices 1) [1,128,256] r1289 c1289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u401
  · exact u402
  · exact m1289_256

def b1290 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 10, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 69 56 176 480 448 448 448), lower := (rows 7 42 69 56 176 32 64 128 256), losses := [] }

theorem u1290 : Upper (D 10) (R 10) [6,40,65,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1290 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1291 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 69 56 400 480 480 480 480), lower := (rows 7 42 69 56 400 32 64 128 256), losses := [] }

theorem u1291 : Upper (D 10) (R 10) [6,40,65,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1291 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1292 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 69 88 176 416 480 416 416), lower := (rows 7 42 69 88 176 32 64 128 256), losses := [] }

theorem u1292 : Upper (D 10) (R 10) [6,40,65,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1292 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1293 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 69 88 400 416 480 416 416), lower := (rows 7 42 69 88 400 32 64 128 256), losses := [] }

theorem u1293 : Upper (D 10) (R 10) [6,40,65,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1293 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1294 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 69 104 176 432 464 400 400), lower := (rows 7 42 69 104 176 32 64 128 256), losses := [] }

theorem u1294 : Upper (D 10) (R 10) [6,40,65,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1294 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1295 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 69 104 400 432 496 432 432), lower := (rows 7 42 69 104 400 32 64 128 256), losses := [] }

theorem u1295 : Upper (D 10) (R 10) [6,40,65,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1295 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1296 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 394, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 42 69 152 112 416 480 416 416), lower := (rows 7 42 69 152 112 32 64 128 256), losses := [] }

theorem u1296 : Upper (D 10) (R 10) [6,40,65,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1296 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1297 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 10, targets := 320 }], pairs := [(1,6),(1,8)], upper := (rows 7 42 69 152 176 352 352 480 352), lower := (rows 7 42 69 152 176 32 64 128 256), losses := [] }

theorem u1297 : Upper (D 10) (R 10) [6,40,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1297 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1298 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 42 69 152 208 288 352 416 288), lower := (rows 7 42 69 152 208 32 64 128 256), losses := [] }

theorem u1298 : Upper (D 10) (R 10) [6,40,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1298 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1299 : Route 9 := (fun mask => (mask,id))

def c1299 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1299 : Upper (D 10) (R 10) [6,40,65,144,288] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,288] 13 (by decide) (choices 1) [64,128,256] r1299 c1299
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u403
  · exact u404
  · exact u405

def b1300 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 42 69 152 336 416 480 416 416), lower := (rows 7 42 69 152 336 32 64 128 256), losses := [] }

theorem u1300 : Upper (D 10) (R 10) [6,40,65,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1300 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1301 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 42 69 152 400 352 352 480 352), lower := (rows 7 42 69 152 400 32 64 128 256), losses := [] }

theorem u1301 : Upper (D 10) (R 10) [6,40,65,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1301 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1302 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 2, targets := 320 }], pairs := [(1,6),(1,8)], upper := (rows 7 42 69 168 176 368 336 464 336), lower := (rows 7 42 69 168 176 32 64 128 256), losses := [] }

theorem u1302 : Upper (D 10) (R 10) [6,40,65,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1302 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1303 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 69 168 304 496 464 464 464), lower := (rows 7 42 69 168 304 32 64 128 256), losses := [] }

theorem u1303 : Upper (D 10) (R 10) [6,40,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1303 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1304 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 69 168 400 368 368 496 368), lower := (rows 7 42 69 168 400 32 64 128 256), losses := [] }

theorem u1304 : Upper (D 10) (R 10) [6,40,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1304 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1305 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 69 200 176 304 368 432 304), lower := (rows 7 42 69 200 176 32 64 128 256), losses := [] }

theorem u1305 : Upper (D 10) (R 10) [6,40,65,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1305 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1306 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 69 200 304 432 496 432 432), lower := (rows 7 42 69 200 304 32 64 128 256), losses := [] }

theorem u1306 : Upper (D 10) (R 10) [6,40,65,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1306 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1307 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 69 200 400 304 368 432 304), lower := (rows 7 42 69 200 400 32 64 128 256), losses := [] }

theorem u1307 : Upper (D 10) (R 10) [6,40,65,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1307 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1308 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 394, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 42 69 392 112 432 496 432 432), lower := (rows 7 42 69 392 112 32 64 128 256), losses := [] }

theorem u1308 : Upper (D 10) (R 10) [6,40,65,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1308 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1309 : Route 9 := (fun mask => (mask,id))

def c1309 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1309 : Upper (D 10) (R 10) [6,40,65,384,160] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,160] 13 (by decide) (choices 1) [16,64,256] r1309 c1309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u406
  · exact u407
  · exact u408

def b1310 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 298, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 42 69 392 208 304 368 432 304), lower := (rows 7 42 69 392 208 32 64 128 256), losses := [] }

theorem u1310 : Upper (D 10) (R 10) [6,40,65,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1310 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1311 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 42 69 392 400 112 112 240 368), lower := (rows 7 42 69 392 400 32 64 128 256), losses := [] }

theorem u1311 : Upper (D 10) (R 10) [6,40,65,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1311 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1312 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 84 41 176 480 448 448 448), lower := (rows 7 42 84 41 176 32 64 128 256), losses := [] }

theorem u1312 : Upper (D 10) (R 10) [6,40,80,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1312 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1313 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 84 41 400 480 480 480 480), lower := (rows 7 42 84 41 400 32 64 128 256), losses := [] }

theorem u1313 : Upper (D 10) (R 10) [6,40,80,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1313 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1314 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 84 73 176 416 480 416 416), lower := (rows 7 42 84 73 176 32 64 128 256), losses := [] }

theorem u1314 : Upper (D 10) (R 10) [6,40,80,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1314 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1315 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 84 73 400 416 480 416 416), lower := (rows 7 42 84 73 400 32 64 128 256), losses := [] }

theorem u1315 : Upper (D 10) (R 10) [6,40,80,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1315 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1316 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 23, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 84 104 49 416 448 384 384), lower := (rows 7 42 84 104 49 32 64 128 256), losses := [] }

theorem u1316 : Upper (D 10) (R 10) [6,40,80,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1316 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1317 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 2, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 7 42 84 104 145 416 480 416 416), lower := (rows 7 42 84 104 145 32 64 128 256), losses := [] }

theorem u1317 : Upper (D 10) (R 10) [6,40,80,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1317 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1318 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 84 104 176 417 449 385 385), lower := (rows 7 42 84 104 176 32 64 128 256), losses := [] }

theorem u1318 : Upper (D 10) (R 10) [6,40,80,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1318 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1319 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 84 104 400 417 481 417 417), lower := (rows 7 42 84 104 400 32 64 128 256), losses := [] }

theorem u1319 : Upper (D 10) (R 10) [6,40,80,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1319 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1319
end Delivery.IrregularNine14.P10
