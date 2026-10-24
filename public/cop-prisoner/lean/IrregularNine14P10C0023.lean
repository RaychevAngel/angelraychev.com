import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0007
import IrregularNine14P10C0008

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1380 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 356, targets := 128 }], pairs := [(2,7),(4,6)], upper := (rows 7 42 100 200 145 304 368 432 304), lower := (rows 7 42 100 200 145 32 64 128 256), losses := [] }

theorem u1380 : Upper (D 10) (R 10) [6,40,96,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1380 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1381 : Route 9 := (fun mask => (mask,id))

def c1381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1381 : Upper (D 10) (R 10) [6,40,96,192,160] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,160] 13 (by decide) (choices 1) [1,16,256] r1381 c1381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u457
  · exact u458
  · exact u459

def r1382 : Route 9 := (fun mask => (mask,id))

def c1382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1382 : Upper (D 10) (R 10) [6,40,96,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,257] 13 (by decide) (choices 1) [16,128,256] r1382 c1382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u460
  · exact u461
  · exact u462

def r1383 : Route 9 := (fun mask => (mask,id))

def c1383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1383 : Upper (D 10) (R 10) [6,40,96,192,288] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,288] 13 (by decide) (choices 1) [1,16,128,256] r1383 c1383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u463
  · exact u464
  · exact u465
  · exact u466

def r1384 : Route 9 := (fun mask => (mask,id))

def c1384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1384 : Upper (D 10) (R 10) [6,40,96,192,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,384] 13 (by decide) (choices 1) [1,16,256] r1384 c1384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u467
  · exact u468
  · exact u469

def r1385 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1385 : Upper (D 10) (R 10) [6,40,96,384,33] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,33] 13 (by decide) (choices 1) [16,64,128] r1385 c1385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u470
  · exact u471
  · exact u472

def b1386 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 42 100 392 81 432 496 432 432), lower := (rows 7 42 100 392 81 32 64 128 256), losses := [] }

theorem u1386 : Upper (D 10) (R 10) [6,40,96,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1386 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1387 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 16, targets := 384 }], pairs := [(4,7),(4,8)], upper := (rows 7 42 100 392 112 433 465 401 401), lower := (rows 7 42 100 392 112 32 64 128 256), losses := [] }

theorem u1387 : Upper (D 10) (R 10) [6,40,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1387 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1388 : Route 9 := (fun mask => (mask,id))

def c1388 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1388 : Upper (D 10) (R 10) [6,40,96,384,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,129] 13 (by decide) (choices 1) [16,64,256] r1388 c1388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u473
  · exact u474
  · exact u475

def r1389 : Route 9 := (fun mask => (mask,id))

def c1389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1389 : Upper (D 10) (R 10) [6,40,96,384,160] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,160] 13 (by decide) (choices 1) [1,16,64,256] r1389 c1389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u476
  · exact u477
  · exact u478
  · exact u479

def r1390 : Route 9 := (fun mask => (mask,id))

def c1390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1390 : Upper (D 10) (R 10) [6,40,96,384,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,192] 13 (by decide) (choices 1) [1,16,256] r1390 c1390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u480
  · exact u481
  · exact u482

def b1391 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 42 100 392 400 113 113 241 369), lower := (rows 7 42 100 392 400 32 64 128 256), losses := [] }

theorem u1391 : Upper (D 10) (R 10) [6,40,96,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1391 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1392 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 41 112 432 464 400 400), lower := (rows 7 42 196 41 112 32 64 128 256), losses := [] }

theorem u1392 : Upper (D 10) (R 10) [6,40,192,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1392 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1393 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 41 304 496 464 464 464), lower := (rows 7 42 196 41 304 32 64 128 256), losses := [] }

theorem u1393 : Upper (D 10) (R 10) [6,40,192,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1393 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1394 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 41 336 432 496 432 432), lower := (rows 7 42 196 41 336 32 64 128 256), losses := [] }

theorem u1394 : Upper (D 10) (R 10) [6,40,192,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1394 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1395 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 10, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 56 49 480 448 448 448), lower := (rows 7 42 196 56 49 32 64 128 256), losses := [] }

theorem u1395 : Upper (D 10) (R 10) [6,40,192,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1395 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1396 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 10, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 56 112 417 449 385 385), lower := (rows 7 42 196 56 112 32 64 128 256), losses := [] }

theorem u1396 : Upper (D 10) (R 10) [6,40,192,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1396 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1397 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 56 273 480 480 480 480), lower := (rows 7 42 196 56 273 32 64 128 256), losses := [] }

theorem u1397 : Upper (D 10) (R 10) [6,40,192,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1397 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1398 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 10, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 56 304 481 449 449 449), lower := (rows 7 42 196 56 304 32 64 128 256), losses := [] }

theorem u1398 : Upper (D 10) (R 10) [6,40,192,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1398 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1399 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 56 336 417 481 417 417), lower := (rows 7 42 196 56 336 32 64 128 256), losses := [] }

theorem u1399 : Upper (D 10) (R 10) [6,40,192,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1399 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1400 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 196 73 176 304 368 432 304), lower := (rows 7 42 196 73 176 32 64 128 256), losses := [] }

theorem u1400 : Upper (D 10) (R 10) [6,40,192,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1400 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1401 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 196 73 304 432 496 432 432), lower := (rows 7 42 196 73 304 32 64 128 256), losses := [] }

theorem u1401 : Upper (D 10) (R 10) [6,40,192,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1401 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1402 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 196 73 400 304 368 432 304), lower := (rows 7 42 196 73 400 32 64 128 256), losses := [] }

theorem u1402 : Upper (D 10) (R 10) [6,40,192,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1402 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1403 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 196 88 49 416 480 416 416), lower := (rows 7 42 196 88 49 32 64 128 256), losses := [] }

theorem u1403 : Upper (D 10) (R 10) [6,40,192,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1403 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1404 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 7 42 196 88 145 288 352 416 288), lower := (rows 7 42 196 88 145 32 64 128 256), losses := [] }

theorem u1404 : Upper (D 10) (R 10) [6,40,192,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1404 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1405 : Route 9 := (fun mask => (mask,id))

def c1405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1405 : Upper (D 10) (R 10) [6,40,192,80,160] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,160] 13 (by decide) (choices 1) [1,256] r1405 c1405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u483
  · exact u484

def b1406 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 196 88 273 416 480 416 416), lower := (rows 7 42 196 88 273 32 64 128 256), losses := [] }

theorem u1406 : Upper (D 10) (R 10) [6,40,192,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1406 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1407 : Route 9 := (fun mask => (mask,id))

def c1407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1407 : Upper (D 10) (R 10) [6,40,192,80,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,288] 13 (by decide) (choices 1) [1,128,256] r1407 c1407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u485
  · exact u486
  · exact u487

def r1408 : Route 9 := (fun mask => (mask,id))

def c1408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1408 : Upper (D 10) (R 10) [6,40,192,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,384] 13 (by decide) (choices 1) [1,256] r1408 c1408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u488
  · exact u489

def b1409 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 104 49 432 464 400 400), lower := (rows 7 42 196 104 49 32 64 128 256), losses := [] }

theorem u1409 : Upper (D 10) (R 10) [6,40,192,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1409 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1410 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 104 176 305 337 401 273), lower := (rows 7 42 196 104 176 32 64 128 256), losses := [] }

theorem u1410 : Upper (D 10) (R 10) [6,40,192,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1410 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1411 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 104 273 432 496 432 432), lower := (rows 7 42 196 104 273 32 64 128 256), losses := [] }

theorem u1411 : Upper (D 10) (R 10) [6,40,192,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1411 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1412 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 104 304 433 465 401 401), lower := (rows 7 42 196 104 304 32 64 128 256), losses := [] }

theorem u1412 : Upper (D 10) (R 10) [6,40,192,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1412 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1413 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 104 400 305 369 433 305), lower := (rows 7 42 196 104 400 32 64 128 256), losses := [] }

theorem u1413 : Upper (D 10) (R 10) [6,40,192,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1413 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1414 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 42 196 200 49 304 368 432 304), lower := (rows 7 42 196 200 49 32 64 128 256), losses := [] }

theorem u1414 : Upper (D 10) (R 10) [6,40,192,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1414 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1415 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 42 196 200 273 304 368 432 304), lower := (rows 7 42 196 200 273 32 64 128 256), losses := [] }

theorem u1415 : Upper (D 10) (R 10) [6,40,192,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1415 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1416 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 42 196 200 304 305 369 433 305), lower := (rows 7 42 196 200 304 32 64 128 256), losses := [] }

theorem u1416 : Upper (D 10) (R 10) [6,40,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1416 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1417 : Route 9 := (fun mask => (mask,id))

def c1417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1417 : Upper (D 10) (R 10) [6,40,192,257,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,96] 13 (by decide) (choices 1) [16,128,256] r1417 c1417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u490
  · exact u491
  · exact u492

def b1418 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 16, targets := 288 }], pairs := [(4,5),(4,8)], upper := (rows 7 42 196 265 208 304 368 432 304), lower := (rows 7 42 196 265 208 32 64 128 256), losses := [] }

theorem u1418 : Upper (D 10) (R 10) [6,40,192,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1418 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1419 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1419 : Upper (D 10) (R 10) [6,40,192,257,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,288] 13 (by decide) (choices 1) [16,64] r1419 c1419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u493
  · exact u494

def r1420 : Route 9 := (fun mask => (mask,id))

def c1420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1420 : Upper (D 10) (R 10) [6,40,192,257,320] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,320] 13 (by decide) (choices 1) [16,128] r1420 c1420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u495
  · exact u496

def r1421 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c1421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1421 : Upper (D 10) (R 10) [6,40,192,272,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,33] 13 (by decide) (choices 1) [64,256] r1421 c1421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u497
  · exact u498

def b1422 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 42 196 280 81 416 480 416 416), lower := (rows 7 42 196 280 81 32 64 128 256), losses := [] }

theorem u1422 : Upper (D 10) (R 10) [6,40,192,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1422 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1423 : Route 9 := (fun mask => (mask,id))

def c1423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1423 : Upper (D 10) (R 10) [6,40,192,272,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,96] 13 (by decide) (choices 1) [1,128,256] r1423 c1423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u499
  · exact u500
  · exact u501

def b1424 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 288 }], pairs := [(4,5),(4,8)], upper := (rows 7 42 196 280 208 289 353 417 289), lower := (rows 7 42 196 280 208 32 64 128 256), losses := [] }

theorem u1424 : Upper (D 10) (R 10) [6,40,192,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1424 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1425 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 196 280 273 224 224 224 480), lower := (rows 7 42 196 280 273 32 64 128 256), losses := [] }

theorem u1425 : Upper (D 10) (R 10) [6,40,192,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1425 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1426 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 10, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 280 304 225 225 225 481), lower := (rows 7 42 196 280 304 32 64 128 256), losses := [] }

theorem u1426 : Upper (D 10) (R 10) [6,40,192,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1426 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1427 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 196 280 336 161 225 161 417), lower := (rows 7 42 196 280 336 32 64 128 256), losses := [] }

theorem u1427 : Upper (D 10) (R 10) [6,40,192,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1427 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1428 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 296 49 496 464 464 464), lower := (rows 7 42 196 296 49 32 64 128 256), losses := [] }

theorem u1428 : Upper (D 10) (R 10) [6,40,192,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1428 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1429 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 296 112 433 465 401 401), lower := (rows 7 42 196 296 112 32 64 128 256), losses := [] }

theorem u1429 : Upper (D 10) (R 10) [6,40,192,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1429 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1430 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 296 273 240 240 240 496), lower := (rows 7 42 196 296 273 32 64 128 256), losses := [] }

theorem u1430 : Upper (D 10) (R 10) [6,40,192,288,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1430 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1431 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 296 304 241 209 209 465), lower := (rows 7 42 196 296 304 32 64 128 256), losses := [] }

theorem u1431 : Upper (D 10) (R 10) [6,40,192,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1431 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1432 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 2, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 42 196 296 336 177 241 177 433), lower := (rows 7 42 196 296 336 32 64 128 256), losses := [] }

theorem u1432 : Upper (D 10) (R 10) [6,40,192,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1432 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1433 : Route 9 := (fun mask => (mask,id))

def c1433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1433 : Upper (D 10) (R 10) [6,40,192,320,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,33] 13 (by decide) (choices 1) [16,128,256] r1433 c1433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u502
  · exact u503
  · exact u504

def b1434 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 7 42 196 328 145 304 368 432 304), lower := (rows 7 42 196 328 145 32 64 128 256), losses := [] }

theorem u1434 : Upper (D 10) (R 10) [6,40,192,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1434 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1435 : Route 9 := (fun mask => (mask,id))

def c1435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1435 : Upper (D 10) (R 10) [6,40,192,320,160] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,160] 13 (by decide) (choices 1) [1,16,256] r1435 c1435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u505
  · exact u506
  · exact u507

def b1436 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 228, targets := 256 }], pairs := [(2,8),(4,6)], upper := (rows 7 42 196 328 273 176 240 176 432), lower := (rows 7 42 196 328 273 32 64 128 256), losses := [] }

theorem u1436 : Upper (D 10) (R 10) [6,40,192,320,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1436 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1437 : Route 9 := (fun mask => (mask,id))

def c1437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1437 : Upper (D 10) (R 10) [6,40,192,320,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,288] 13 (by decide) (choices 1) [1,16,128] r1437 c1437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u508
  · exact u509
  · exact u510

def r1438 : Route 9 := (fun mask => (mask,id))

def c1438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1438 : Upper (D 10) (R 10) [6,40,192,320,384] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,384] 13 (by decide) (choices 1) [1,16] r1438 c1438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u511
  · exact u512

def b1439 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 76 56 400 416 480 416 416), lower := (rows 7 67 76 56 400 32 64 128 256), losses := [] }

theorem u1439 : Upper (D 10) (R 10) [6,65,72,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1439 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1439
end Delivery.IrregularNine14.P10
