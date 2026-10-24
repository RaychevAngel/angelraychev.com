import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0006
import IrregularNine14P10C0007

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1320 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 84 137 112 416 480 416 416), lower := (rows 7 42 84 137 112 32 64 128 256), losses := [] }

theorem u1320 : Upper (D 10) (R 10) [6,40,80,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1320 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1321 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 354, targets := 128 },{ cop := 4, region := 324, targets := 128 }], pairs := [(1,7),(2,7)], upper := (rows 7 42 84 137 176 352 352 480 352), lower := (rows 7 42 84 137 176 32 64 128 256), losses := [] }

theorem u1321 : Upper (D 10) (R 10) [6,40,80,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1321 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1322 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 84 137 208 288 352 416 288), lower := (rows 7 42 84 137 208 32 64 128 256), losses := [] }

theorem u1322 : Upper (D 10) (R 10) [6,40,80,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1322 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1323 : Route 9 := (fun mask => (mask,id))

def c1323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1323 : Upper (D 10) (R 10) [6,40,80,129,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,288] 13 (by decide) (choices 1) [64,128,256] r1323 c1323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u409
  · exact u410
  · exact u411

def b1324 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 84 137 336 416 480 416 416), lower := (rows 7 42 84 137 336 32 64 128 256), losses := [] }

theorem u1324 : Upper (D 10) (R 10) [6,40,80,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1324 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1325 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 354, targets := 128 },{ cop := 4, region := 100, targets := 128 }], pairs := [(1,7),(2,7)], upper := (rows 7 42 84 137 400 352 352 480 352), lower := (rows 7 42 84 137 400 32 64 128 256), losses := [] }

theorem u1325 : Upper (D 10) (R 10) [6,40,80,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1325 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1326 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 84 168 49 480 448 448 448), lower := (rows 7 42 84 168 49 32 64 128 256), losses := [] }

theorem u1326 : Upper (D 10) (R 10) [6,40,80,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1326 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1327 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 2, targets := 320 }], pairs := [(1,6),(1,8)], upper := (rows 7 42 84 168 145 352 352 480 352), lower := (rows 7 42 84 168 145 32 64 128 256), losses := [] }

theorem u1327 : Upper (D 10) (R 10) [6,40,80,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1327 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1328 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 2, targets := 320 }], pairs := [(1,6),(1,8)], upper := (rows 7 42 84 168 176 353 321 449 321), lower := (rows 7 42 84 168 176 32 64 128 256), losses := [] }

theorem u1328 : Upper (D 10) (R 10) [6,40,80,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1328 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1329 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 84 168 273 480 480 480 480), lower := (rows 7 42 84 168 273 32 64 128 256), losses := [] }

theorem u1329 : Upper (D 10) (R 10) [6,40,80,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1329 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1330 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 84 168 304 481 449 449 449), lower := (rows 7 42 84 168 304 32 64 128 256), losses := [] }

theorem u1330 : Upper (D 10) (R 10) [6,40,80,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1330 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1331 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 84 168 400 353 353 481 353), lower := (rows 7 42 84 168 400 32 64 128 256), losses := [] }

theorem u1331 : Upper (D 10) (R 10) [6,40,80,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1331 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1332 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 3, region := 290, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 84 200 49 416 480 416 416), lower := (rows 7 42 84 200 49 32 64 128 256), losses := [] }

theorem u1332 : Upper (D 10) (R 10) [6,40,80,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1332 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1333 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 3, region := 290, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 84 200 145 288 352 416 288), lower := (rows 7 42 84 200 145 32 64 128 256), losses := [] }

theorem u1333 : Upper (D 10) (R 10) [6,40,80,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1333 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1334 : Route 9 := (fun mask => (mask,id))

def c1334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1334 : Upper (D 10) (R 10) [6,40,80,192,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,160] 13 (by decide) (choices 1) [1,256] r1334 c1334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u412
  · exact u413

def b1335 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 3, region := 290, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 84 200 273 416 480 416 416), lower := (rows 7 42 84 200 273 32 64 128 256), losses := [] }

theorem u1335 : Upper (D 10) (R 10) [6,40,80,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1335 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1336 : Route 9 := (fun mask => (mask,id))

def c1336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1336 : Upper (D 10) (R 10) [6,40,80,192,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,288] 13 (by decide) (choices 1) [1,128,256] r1336 c1336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u414
  · exact u415
  · exact u416

def r1337 : Route 9 := (fun mask => (mask,id))

def c1337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1337 : Upper (D 10) (R 10) [6,40,80,192,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,384] 13 (by decide) (choices 1) [1,256] r1337 c1337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u417
  · exact u418

def r1338 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1338 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1338 : Upper (D 10) (R 10) [6,40,80,384,33] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,33] 13 (by decide) (choices 1) [64,128] r1338 c1338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u419
  · exact u420

def b1339 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 84 392 81 416 480 416 416), lower := (rows 7 42 84 392 81 32 64 128 256), losses := [] }

theorem u1339 : Upper (D 10) (R 10) [6,40,80,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1339 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1340 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 84 392 112 417 481 417 417), lower := (rows 7 42 84 392 112 32 64 128 256), losses := [] }

theorem u1340 : Upper (D 10) (R 10) [6,40,80,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1340 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1341 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 98, targets := 128 },{ cop := 4, region := 356, targets := 128 }], pairs := [(1,7),(2,7)], upper := (rows 7 42 84 392 145 352 352 480 352), lower := (rows 7 42 84 392 145 32 64 128 256), losses := [] }

theorem u1341 : Upper (D 10) (R 10) [6,40,80,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1341 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1342 : Route 9 := (fun mask => (mask,id))

def c1342 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1342 : Upper (D 10) (R 10) [6,40,80,384,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,160] 13 (by decide) (choices 1) [1,64,256] r1342 c1342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u421
  · exact u422
  · exact u423

def b1343 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 84 392 208 289 353 417 289), lower := (rows 7 42 84 392 208 32 64 128 256), losses := [] }

theorem u1343 : Upper (D 10) (R 10) [6,40,80,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1343 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1344 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 42 84 392 400 97 97 225 353), lower := (rows 7 42 84 392 400 32 64 128 256), losses := [] }

theorem u1344 : Upper (D 10) (R 10) [6,40,80,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1344 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1345 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 11, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 42 100 41 208 432 464 400 400), lower := (rows 7 42 100 41 208 32 64 128 256), losses := [] }

theorem u1345 : Upper (D 10) (R 10) [6,40,96,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1345 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1346 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 11, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 42 100 41 400 496 464 464 464), lower := (rows 7 42 100 41 400 32 64 128 256), losses := [] }

theorem u1346 : Upper (D 10) (R 10) [6,40,96,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1346 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1347 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 100 56 145 480 448 448 448), lower := (rows 7 42 100 56 145 32 64 128 256), losses := [] }

theorem u1347 : Upper (D 10) (R 10) [6,40,96,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1347 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1348 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 100 56 208 417 449 385 385), lower := (rows 7 42 100 56 208 32 64 128 256), losses := [] }

theorem u1348 : Upper (D 10) (R 10) [6,40,96,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1348 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1349 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 100 56 400 481 449 449 449), lower := (rows 7 42 100 56 400 32 64 128 256), losses := [] }

theorem u1349 : Upper (D 10) (R 10) [6,40,96,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1349 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1350 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 100 73 176 432 464 400 400), lower := (rows 7 42 100 73 176 32 64 128 256), losses := [] }

theorem u1350 : Upper (D 10) (R 10) [6,40,96,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1350 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1351 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 100 73 400 432 496 432 432), lower := (rows 7 42 100 73 400 32 64 128 256), losses := [] }

theorem u1351 : Upper (D 10) (R 10) [6,40,96,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1351 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1352 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 27, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 100 88 49 416 448 384 384), lower := (rows 7 42 100 88 49 32 64 128 256), losses := [] }

theorem u1352 : Upper (D 10) (R 10) [6,40,96,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1352 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1353 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 100 88 145 416 480 416 416), lower := (rows 7 42 100 88 145 32 64 128 256), losses := [] }

theorem u1353 : Upper (D 10) (R 10) [6,40,96,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1353 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1354 : Route 9 := (fun mask => (mask,id))

def c1354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1354 : Upper (D 10) (R 10) [6,40,96,80,160] 13 := by
  apply FastRouting.sound _ _ [6,40,96,80,160] 13 (by decide) (choices 1) [1,128,256] r1354 c1354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u424
  · exact u425
  · exact u426

def r1355 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1355 : Upper (D 10) (R 10) [6,40,96,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,80,384] 13 (by decide) (choices 1) [1,128] r1355 c1355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u427
  · exact u428

def b1356 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 100 104 145 432 464 400 400), lower := (rows 7 42 100 104 145 32 64 128 256), losses := [] }

theorem u1356 : Upper (D 10) (R 10) [6,40,96,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1356 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1357 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 100 104 400 433 465 401 401), lower := (rows 7 42 100 104 400 32 64 128 256), losses := [] }

theorem u1357 : Upper (D 10) (R 10) [6,40,96,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1357 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1358 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 16, targets := 384 }], pairs := [(4,7),(4,8)], upper := (rows 7 42 100 137 112 432 464 400 400), lower := (rows 7 42 100 137 112 32 64 128 256), losses := [] }

theorem u1358 : Upper (D 10) (R 10) [6,40,96,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1358 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1359 : Route 9 := (fun mask => (mask,id))

def c1359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1359 : Upper (D 10) (R 10) [6,40,96,129,160] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,160] 13 (by decide) (choices 1) [16,64,256] r1359 c1359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u429
  · exact u430
  · exact u431

def r1360 : Route 9 := (fun mask => (mask,id))

def c1360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1360 : Upper (D 10) (R 10) [6,40,96,129,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,192] 13 (by decide) (choices 1) [16,256] r1360 c1360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u432
  · exact u433

def r1361 : Route 9 := (fun mask => (mask,id))

def c1361 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1361 : Upper (D 10) (R 10) [6,40,96,129,288] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,288] 13 (by decide) (choices 1) [16,64,128,256] r1361 c1361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u434
  · exact u435
  · exact u436
  · exact u437

def r1362 : Route 9 := (fun mask => (mask,id))

def c1362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1362 : Upper (D 10) (R 10) [6,40,96,129,320] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,320] 13 (by decide) (choices 1) [16,128,256] r1362 c1362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u438
  · exact u439
  · exact u440

def r1363 : Route 9 := (fun mask => (mask,id))

def c1363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1363 : Upper (D 10) (R 10) [6,40,96,129,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,384] 13 (by decide) (choices 1) [16,64,256] r1363 c1363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u441
  · exact u442
  · exact u443

def r1364 : Route 9 := (fun mask => (mask,id))

def c1364 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1364 : Upper (D 10) (R 10) [6,40,96,144,33] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,33] 13 (by decide) (choices 1) [64,128,256] r1364 c1364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u444
  · exact u445
  · exact u446

def b1365 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 42 100 152 81 416 480 416 416), lower := (rows 7 42 100 152 81 32 64 128 256), losses := [] }

theorem u1365 : Upper (D 10) (R 10) [6,40,96,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1365 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1366 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 16, targets := 384 }], pairs := [(4,7),(4,8)], upper := (rows 7 42 100 152 112 417 449 385 385), lower := (rows 7 42 100 152 112 32 64 128 256), losses := [] }

theorem u1366 : Upper (D 10) (R 10) [6,40,96,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1366 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1367 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 42 100 152 145 352 352 480 352), lower := (rows 7 42 100 152 145 32 64 128 256), losses := [] }

theorem u1367 : Upper (D 10) (R 10) [6,40,96,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1367 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1368 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 10, targets := 320 }], pairs := [(1,6),(1,8)], upper := (rows 7 42 100 152 176 353 321 449 321), lower := (rows 7 42 100 152 176 32 64 128 256), losses := [] }

theorem u1368 : Upper (D 10) (R 10) [6,40,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1368 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1369 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 42 100 152 208 289 353 417 289), lower := (rows 7 42 100 152 208 32 64 128 256), losses := [] }

theorem u1369 : Upper (D 10) (R 10) [6,40,96,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1369 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1370 : Route 9 := (fun mask => (mask,id))

def c1370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1370 : Upper (D 10) (R 10) [6,40,96,144,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,257] 13 (by decide) (choices 1) [64,128,256] r1370 c1370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u447
  · exact u448
  · exact u449

def r1371 : Route 9 := (fun mask => (mask,id))

def c1371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1371 : Upper (D 10) (R 10) [6,40,96,144,288] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,288] 13 (by decide) (choices 1) [1,64,128,256] r1371 c1371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u450
  · exact u451
  · exact u452
  · exact u453

def r1372 : Route 9 := (fun mask => (mask,id))

def c1372 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1372 : Upper (D 10) (R 10) [6,40,96,144,320] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,320] 13 (by decide) (choices 1) [1,128,256] r1372 c1372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u454
  · exact u455
  · exact u456

def b1373 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 42 100 152 400 353 353 481 353), lower := (rows 7 42 100 152 400 32 64 128 256), losses := [] }

theorem u1373 : Upper (D 10) (R 10) [6,40,96,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1373 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1374 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 100 168 145 368 336 464 336), lower := (rows 7 42 100 168 145 32 64 128 256), losses := [] }

theorem u1374 : Upper (D 10) (R 10) [6,40,96,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1374 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1375 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 100 168 208 305 337 401 273), lower := (rows 7 42 100 168 208 32 64 128 256), losses := [] }

theorem u1375 : Upper (D 10) (R 10) [6,40,96,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1375 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1376 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 100 168 273 496 464 464 464), lower := (rows 7 42 100 168 273 32 64 128 256), losses := [] }

theorem u1376 : Upper (D 10) (R 10) [6,40,96,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1376 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1377 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 100 168 336 433 465 401 401), lower := (rows 7 42 100 168 336 32 64 128 256), losses := [] }

theorem u1377 : Upper (D 10) (R 10) [6,40,96,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1377 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1378 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 100 168 400 369 337 465 337), lower := (rows 7 42 100 168 400 32 64 128 256), losses := [] }

theorem u1378 : Upper (D 10) (R 10) [6,40,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1378 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1379 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 456, targets := 32 }], pairs := [(3,5),(4,6)], upper := (rows 7 42 100 200 49 432 464 400 400), lower := (rows 7 42 100 200 49 32 64 128 256), losses := [] }

theorem u1379 : Upper (D 10) (R 10) [6,40,96,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1379 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1379
end Delivery.IrregularNine14.P10
