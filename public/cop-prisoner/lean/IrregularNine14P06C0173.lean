import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0021

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r10380 : Route 9 := (fun mask => (mask,id))

def c10380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10380 : Upper (D 6) (R 6) [6,40,129,320,68,1] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320,68,1] 13 (by decide) (choices 1) [2,16,32] r10380 c10380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1268
  · exact u1269
  · exact u1270

def b10381 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 133 328 84 34 113 177 305), lower := (rows 7 42 133 328 84 34 64 128 256), losses := [] }

theorem u10381 : Upper (D 6) (R 6) [6,40,129,320,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10381
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10382 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 42 133 328 84 48 99 163 291), lower := (rows 7 42 133 328 84 48 64 128 256), losses := [] }

theorem u10382 : Upper (D 6) (R 6) [6,40,129,320,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10382
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10383 : Route 9 := (fun mask => (mask,id))

def c10383 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10383 : Upper (D 6) (R 6) [6,40,129,320,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320,96,1] 13 (by decide) (choices 1) [2,4,16] r10383 c10383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1271
  · exact u1272
  · exact u1273

def b10384 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 42 133 328 112 34 85 149 277), lower := (rows 7 42 133 328 112 34 64 128 256), losses := [] }

theorem u10384 : Upper (D 6) (R 6) [6,40,129,320,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10384
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10385 : Route 9 := (fun mask => (mask,id))

def c10385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10385 : Upper (D 6) (R 6) [6,40,129,320,96,4] 13 := by
  apply FastRouting.sound _ _ [6,40,129,320,96,4] 13 (by decide) (choices 1) [1,2,16] r10385 c10385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1274
  · exact u1275
  · exact u1276

def b10386 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 133 328 112 48 71 135 263), lower := (rows 7 42 133 328 112 48 64 128 256), losses := [] }

theorem u10386 : Upper (D 6) (R 6) [6,40,129,320,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10386
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10387 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 148 73 112 33 326 390 262), lower := (rows 7 42 148 73 112 33 64 128 256), losses := [] }

theorem u10387 : Upper (D 6) (R 6) [6,40,144,65,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10387
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10388 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 50, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 42 148 73 112 34 325 389 261), lower := (rows 7 42 148 73 112 34 64 128 256), losses := [] }

theorem u10388 : Upper (D 6) (R 6) [6,40,144,65,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10388
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10389 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 328, targets := 36 }], pairs := [(1,0),(3,2),(3,5)], upper := (rows 7 42 148 73 112 36 323 387 259), lower := (rows 7 42 148 73 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 24 37 64 128 256), good := (rows 38 58 180 122 112 36 64 128 256) }] }

theorem u10389 : Upper (D 6) (R 6) [6,40,144,65,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10389
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10390 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(1,6),(3,5)], upper := (rows 7 42 148 73 112 288 71 135 263), lower := (rows 7 42 148 73 112 288 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 16 297 0 129 257), good := (rows 423 42 148 427 48 288 0 128 288) }] }

theorem u10390 : Upper (D 6) (R 6) [6,40,144,65,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10390
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10391 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 148 73 273 34 100 228 356), lower := (rows 7 42 148 73 273 34 64 128 256), losses := [] }

theorem u10391 : Upper (D 6) (R 6) [6,40,144,65,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10391
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10392 : PairBound 9 := { available := 98, camps := [], pairs := [(1,0),(2,0),(3,2)], upper := (rows 7 42 148 73 273 36 98 226 354), lower := (rows 7 42 148 73 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 53 75 139 267), good := (rows 486 490 180 490 500 36 64 128 256) },{ target := 2, region := (rows 1 2 0 9 17 32 66 130 258), good := (rows 475 490 144 89 281 32 64 128 256) }] }

theorem u10392 : Upper (D 6) (R 6) [6,40,144,65,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10392
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10393 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 148 73 273 96 102 166 294), lower := (rows 7 42 148 73 273 96 64 128 256), losses := [] }

theorem u10393 : Upper (D 6) (R 6) [6,40,144,65,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10393
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10394 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 148 73 274 33 100 228 356), lower := (rows 7 42 148 73 274 33 64 128 256), losses := [] }

theorem u10394 : Upper (D 6) (R 6) [6,40,144,65,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10394
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10395 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 104, targets := 2 }], pairs := [(1,0),(1,6),(3,1)], upper := (rows 7 42 148 73 274 36 97 225 353), lower := (rows 7 42 148 73 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 180 106 274 36 64 128 256) },{ target := 6, region := (rows 1 10 4 8 16 37 0 128 256), good := (rows 39 42 180 43 274 36 0 128 256) }] }

theorem u10395 : Upper (D 6) (R 6) [6,40,144,65,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10395
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10396 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 148 73 274 96 101 165 293), lower := (rows 7 42 148 73 274 96 64 128 256), losses := [] }

theorem u10396 : Upper (D 6) (R 6) [6,40,144,65,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10396
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10397 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 106, targets := 4 },{ cop := 1, region := 468, targets := 1 }], pairs := [(1,2),(2,0),(3,2)], upper := (rows 7 42 148 73 276 33 98 226 354), lower := (rows 7 42 148 73 276 33 64 128 256), losses := [] }

theorem u10397 : Upper (D 6) (R 6) [6,40,144,65,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10397
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10398 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 106, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(1,2),(3,2)], upper := (rows 7 42 148 73 276 34 97 225 353), lower := (rows 7 42 148 73 276 34 64 128 256), losses := [] }

theorem u10398 : Upper (D 6) (R 6) [6,40,144,65,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10398
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10399 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 148 73 276 96 99 163 291), lower := (rows 7 42 148 73 276 96 64 128 256), losses := [] }

theorem u10399 : Upper (D 6) (R 6) [6,40,144,65,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10399
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10400 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 148 73 304 33 70 198 326), lower := (rows 7 42 148 73 304 33 64 128 256), losses := [] }

theorem u10400 : Upper (D 6) (R 6) [6,40,144,65,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10400
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10401 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 148 73 304 34 69 197 325), lower := (rows 7 42 148 73 304 34 64 128 256), losses := [] }

theorem u10401 : Upper (D 6) (R 6) [6,40,144,65,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10401
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10402 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(1,0),(3,2),(3,5)], upper := (rows 7 42 148 73 304 36 67 195 323), lower := (rows 7 42 148 73 304 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 180 106 304 36 64 128 256) }] }

theorem u10402 : Upper (D 6) (R 6) [6,40,144,65,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10402
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10403 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 148 73 304 96 71 135 263), lower := (rows 7 42 148 73 304 96 64 128 256), losses := [] }

theorem u10403 : Upper (D 6) (R 6) [6,40,144,65,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10403
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10404 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 148 73 336 33 102 166 294), lower := (rows 7 42 148 73 336 33 64 128 256), losses := [] }

theorem u10404 : Upper (D 6) (R 6) [6,40,144,65,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10404
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10405 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 148 73 336 34 101 165 293), lower := (rows 7 42 148 73 336 34 64 128 256), losses := [] }

theorem u10405 : Upper (D 6) (R 6) [6,40,144,65,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10405
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10406 : Route 9 := (fun mask => (mask,id))

def c10406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10406 : Upper (D 6) (R 6) [6,40,144,65,320,4] 13 := by
  apply FastRouting.sound _ _ [6,40,144,65,320,4] 13 (by decide) (choices 1) [1,2,32] r10406 c10406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1277
  · exact u1278
  · exact u1279

def r10407 : Route 9 := (fun mask => (mask,id))

def c10407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10407 : Upper (D 6) (R 6) [6,40,144,66,257,1] 13 := by
  apply FastRouting.sound _ _ [6,40,144,66,257,1] 13 (by decide) (choices 1) [4,32] r10407 c10407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1280
  · exact u1281

def r10408 : Route 9 := (fun mask => (mask,id))

def c10408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10408 : Upper (D 6) (R 6) [6,40,144,66,257,4] 13 := by
  apply FastRouting.sound _ _ [6,40,144,66,257,4] 13 (by decide) (choices 1) [1,32] r10408 c10408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1282
  · exact u1283

def b10409 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 42 148 74 273 96 101 165 293), lower := (rows 7 42 148 74 273 96 64 128 256), losses := [] }

theorem u10409 : Upper (D 6) (R 6) [6,40,144,66,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10409
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10410 : Route 9 := (fun mask => (mask,id))

def c10410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10410 : Upper (D 6) (R 6) [6,40,144,66,320,1] 13 := by
  apply FastRouting.sound _ _ [6,40,144,66,320,1] 13 (by decide) (choices 1) [1,4,32] r10410 c10410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1284
  · exact u1285
  · exact u1286

def r10411 : Route 9 := (fun mask => (mask,id))

def c10411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10411 : Upper (D 6) (R 6) [6,40,144,66,320,4] 13 := by
  apply FastRouting.sound _ _ [6,40,144,66,320,4] 13 (by decide) (choices 1) [1,32] r10411 c10411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1287
  · exact u1288

def b10412 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 148 76 273 33 98 226 354), lower := (rows 7 42 148 76 273 33 64 128 256), losses := [] }

theorem u10412 : Upper (D 6) (R 6) [6,40,144,68,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10412
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10413 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 148 76 273 34 97 225 353), lower := (rows 7 42 148 76 273 34 64 128 256), losses := [] }

theorem u10413 : Upper (D 6) (R 6) [6,40,144,68,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10413
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10414 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 148 76 273 96 99 163 291), lower := (rows 7 42 148 76 273 96 64 128 256), losses := [] }

theorem u10414 : Upper (D 6) (R 6) [6,40,144,68,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10414
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10415 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 104, targets := 2 }], pairs := [(0,6),(1,6),(3,1)], upper := (rows 7 42 148 76 274 33 97 225 353), lower := (rows 7 42 148 76 274 33 64 128 256), losses := [] }

theorem u10415 : Upper (D 6) (R 6) [6,40,144,68,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10415
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10416 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 148 76 274 96 97 161 289), lower := (rows 7 42 148 76 274 96 64 128 256), losses := [] }

theorem u10416 : Upper (D 6) (R 6) [6,40,144,68,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10416
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10417 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 148 76 304 33 67 195 323), lower := (rows 7 42 148 76 304 33 64 128 256), losses := [] }

theorem u10417 : Upper (D 6) (R 6) [6,40,144,68,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10417
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10418 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 72, targets := 34 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(3,1),(3,5)], upper := (rows 7 42 148 76 304 34 65 193 321), lower := (rows 7 42 148 76 304 34 64 128 256), losses := [] }

theorem u10418 : Upper (D 6) (R 6) [6,40,144,68,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10418
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10419 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 42 148 76 304 96 67 131 259), lower := (rows 7 42 148 76 304 96 64 128 256), losses := [] }

theorem u10419 : Upper (D 6) (R 6) [6,40,144,68,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10419
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10420 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 148 265 81 34 100 228 356), lower := (rows 7 42 148 265 81 34 64 128 256), losses := [] }

theorem u10420 : Upper (D 6) (R 6) [6,40,144,257,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10420
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10421 : PairBound 9 := { available := 98, camps := [], pairs := [(1,0),(2,0),(3,2)], upper := (rows 7 42 148 265 81 36 98 226 354), lower := (rows 7 42 148 265 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 53 75 139 267), good := (rows 486 490 180 490 500 36 64 128 256) },{ target := 2, region := (rows 1 2 0 9 17 32 66 130 258), good := (rows 475 490 144 281 89 32 64 128 256) }] }

theorem u10421 : Upper (D 6) (R 6) [6,40,144,257,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10421
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10422 : Route 9 := (fun mask => (mask,id))

def c10422 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10422 : Upper (D 6) (R 6) [6,40,144,257,65,64] 13 := by
  apply FastRouting.sound _ _ [6,40,144,257,65,64] 13 (by decide) (choices 1) [2,4,32] r10422 c10422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1289
  · exact u1290
  · exact u1291

def b10423 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 148 265 82 33 100 228 356), lower := (rows 7 42 148 265 82 33 64 128 256), losses := [] }

theorem u10423 : Upper (D 6) (R 6) [6,40,144,257,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10423
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10424 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 360, targets := 2 }], pairs := [(1,0),(1,6),(3,1)], upper := (rows 7 42 148 265 82 36 97 225 353), lower := (rows 7 42 148 265 82 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 180 298 82 36 64 128 256) },{ target := 6, region := (rows 1 10 4 8 16 37 0 128 256), good := (rows 39 42 180 299 18 36 0 128 256) }] }

theorem u10424 : Upper (D 6) (R 6) [6,40,144,257,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10424
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10425 : Route 9 := (fun mask => (mask,id))

def c10425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10425 : Upper (D 6) (R 6) [6,40,144,257,66,64] 13 := by
  apply FastRouting.sound _ _ [6,40,144,257,66,64] 13 (by decide) (choices 1) [1,4,32] r10425 c10425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1292
  · exact u1293
  · exact u1294

def b10426 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 1, region := 212, targets := 1 }], pairs := [(1,2),(2,0),(3,2)], upper := (rows 7 42 148 265 84 33 98 226 354), lower := (rows 7 42 148 265 84 33 64 128 256), losses := [] }

theorem u10426 : Upper (D 6) (R 6) [6,40,144,257,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10426
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10427 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 362, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(1,2),(3,2)], upper := (rows 7 42 148 265 84 34 97 225 353), lower := (rows 7 42 148 265 84 34 64 128 256), losses := [] }

theorem u10427 : Upper (D 6) (R 6) [6,40,144,257,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10427
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10428 : Route 9 := (fun mask => (mask,id))

def c10428 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10428 : Upper (D 6) (R 6) [6,40,144,257,68,64] 13 := by
  apply FastRouting.sound _ _ [6,40,144,257,68,64] 13 (by decide) (choices 1) [1,2,32] r10428 c10428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1295
  · exact u1296
  · exact u1297

def b10429 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 42 148 265 112 33 70 198 326), lower := (rows 7 42 148 265 112 33 64 128 256), losses := [] }

theorem u10429 : Upper (D 6) (R 6) [6,40,144,257,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10429
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10430 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 7 42 148 265 112 34 69 197 325), lower := (rows 7 42 148 265 112 34 64 128 256), losses := [] }

theorem u10430 : Upper (D 6) (R 6) [6,40,144,257,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10430
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10431 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 328, targets := 36 }], pairs := [(1,0),(3,2),(3,5)], upper := (rows 7 42 148 265 112 36 67 195 323), lower := (rows 7 42 148 265 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 180 298 112 36 64 128 256) }] }

theorem u10431 : Upper (D 6) (R 6) [6,40,144,257,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10431
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10432 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 42 148 265 112 96 71 135 263), lower := (rows 7 42 148 265 112 96 64 128 256), losses := [] }

theorem u10432 : Upper (D 6) (R 6) [6,40,144,257,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10432
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10433 : Route 9 := (fun mask => (mask,id))

def c10433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10433 : Upper (D 6) (R 6) [6,40,144,258,65,1] 13 := by
  apply FastRouting.sound _ _ [6,40,144,258,65,1] 13 (by decide) (choices 1) [4,32] r10433 c10433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1298
  · exact u1299

def r10434 : Route 9 := (fun mask => (mask,id))

def c10434 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10434 : Upper (D 6) (R 6) [6,40,144,258,65,4] 13 := by
  apply FastRouting.sound _ _ [6,40,144,258,65,4] 13 (by decide) (choices 1) [1,32] r10434 c10434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1300
  · exact u1301

def r10435 : Route 9 := (fun mask => (mask,id))

def c10435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10435 : Upper (D 6) (R 6) [6,40,144,258,65,64] 13 := by
  apply FastRouting.sound _ _ [6,40,144,258,65,64] 13 (by decide) (choices 1) [1,4,32] r10435 c10435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1302
  · exact u1303
  · exact u1304

def b10436 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 7 42 148 268 81 33 98 226 354), lower := (rows 7 42 148 268 81 33 64 128 256), losses := [] }

theorem u10436 : Upper (D 6) (R 6) [6,40,144,260,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10436
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b10437 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 34, targets := 5 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 7 42 148 268 81 34 97 225 353), lower := (rows 7 42 148 268 81 34 64 128 256), losses := [] }

theorem u10437 : Upper (D 6) (R 6) [6,40,144,260,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10437
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r10438 : Route 9 := (fun mask => (mask,id))

def c10438 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10438 : Upper (D 6) (R 6) [6,40,144,260,65,64] 13 := by
  apply FastRouting.sound _ _ [6,40,144,260,65,64] 13 (by decide) (choices 1) [1,2,32] r10438 c10438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1305
  · exact u1306
  · exact u1307

def b10439 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 360, targets := 2 }], pairs := [(0,6),(1,6),(3,1)], upper := (rows 7 42 148 268 82 33 97 225 353), lower := (rows 7 42 148 268 82 33 64 128 256), losses := [] }

theorem u10439 : Upper (D 6) (R 6) [6,40,144,260,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b10439
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u10439
end Delivery.IrregularNine14.P06
