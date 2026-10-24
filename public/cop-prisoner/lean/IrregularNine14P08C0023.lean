import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0002

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1380 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 74 164 41 304 48 193 193 449), lower := (rows 7 74 164 41 304 48 64 128 256), losses := [] }

theorem u1380 : Upper (D 8) (R 8) [6,72,160,33,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1380 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1381 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 41 304 96 209 145 401), lower := (rows 7 74 164 41 304 96 64 128 256), losses := [] }

theorem u1381 : Upper (D 8) (R 8) [6,72,160,33,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1382 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 41 304 160 81 209 337), lower := (rows 7 74 164 41 304 160 64 128 256), losses := [] }

theorem u1382 : Upper (D 8) (R 8) [6,72,160,33,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1382 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1383 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 41 336 33 240 176 432), lower := (rows 7 74 164 41 336 33 64 128 256), losses := [] }

theorem u1383 : Upper (D 8) (R 8) [6,72,160,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1384 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 74 164 41 336 48 225 161 417), lower := (rows 7 74 164 41 336 48 64 128 256), losses := [] }

theorem u1384 : Upper (D 8) (R 8) [6,72,160,33,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1384 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1385 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 41 336 160 113 177 305), lower := (rows 7 74 164 41 336 160 64 128 256), losses := [] }

theorem u1385 : Upper (D 8) (R 8) [6,72,160,33,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1386 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 41 400 33 112 240 368), lower := (rows 7 74 164 41 400 33 64 128 256), losses := [] }

theorem u1386 : Upper (D 8) (R 8) [6,72,160,33,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1387 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 74 164 41 400 48 97 225 353), lower := (rows 7 74 164 41 400 48 64 128 256), losses := [] }

theorem u1387 : Upper (D 8) (R 8) [6,72,160,33,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1387 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1388 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 41 400 96 113 177 305), lower := (rows 7 74 164 41 400 96 64 128 256), losses := [] }

theorem u1388 : Upper (D 8) (R 8) [6,72,160,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1388 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1389 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 56 273 33 224 224 480), lower := (rows 7 74 164 56 273 33 64 128 256), losses := [] }

theorem u1389 : Upper (D 8) (R 8) [6,72,160,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1390 : Route 9 := (fun mask => (mask,id))

def c1390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1390 : Upper (D 8) (R 8) [6,72,160,48,257,64] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,257,64] 13 (by decide) (choices 1) [1,32,128] r1390 c1390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u148
  · exact u149
  · exact u150

def b1391 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 56 273 160 97 225 353), lower := (rows 7 74 164 56 273 160 64 128 256), losses := [] }

theorem u1391 : Upper (D 8) (R 8) [6,72,160,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1391 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1392 : PairBound 9 := { available := 97, camps := [], pairs := [(1,7)], upper := (rows 7 74 164 56 400 33 97 225 353), lower := (rows 7 74 164 56 400 33 64 128 256), losses := [{ target := 7, region := (rows 1 10 4 8 16 33 97 0 289), good := (rows 359 74 356 378 272 353 64 0 256) }] }

theorem u1392 : Upper (D 8) (R 8) [6,72,160,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1393 : Route 9 := (fun mask => (mask,id))

def c1393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1393 : Upper (D 8) (R 8) [6,72,160,48,384,64] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,384,64] 13 (by decide) (choices 1) [1,32] r1393 c1393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u151
  · exact u152

def b1394 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 265 112 33 240 176 432), lower := (rows 7 74 164 265 112 33 64 128 256), losses := [] }

theorem u1394 : Upper (D 8) (R 8) [6,72,160,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1394 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1395 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 74 164 265 112 48 225 161 417), lower := (rows 7 74 164 265 112 48 64 128 256), losses := [] }

theorem u1395 : Upper (D 8) (R 8) [6,72,160,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1395 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1396 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 265 112 160 113 177 305), lower := (rows 7 74 164 265 112 160 64 128 256), losses := [] }

theorem u1396 : Upper (D 8) (R 8) [6,72,160,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1397 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 265 208 33 112 176 304), lower := (rows 7 74 164 265 208 33 64 128 256), losses := [] }

theorem u1397 : Upper (D 8) (R 8) [6,72,160,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1397 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1398 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 74 164 265 208 48 97 161 289), lower := (rows 7 74 164 265 208 48 64 128 256), losses := [] }

theorem u1398 : Upper (D 8) (R 8) [6,72,160,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1398 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1399 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 280 49 33 224 224 480), lower := (rows 7 74 164 280 49 33 64 128 256), losses := [] }

theorem u1399 : Upper (D 8) (R 8) [6,72,160,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1399 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1400 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 132, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 280 49 96 225 161 417), lower := (rows 7 74 164 280 49 96 64 128 256), losses := [] }

theorem u1400 : Upper (D 8) (R 8) [6,72,160,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1400 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1401 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 280 49 160 97 225 353), lower := (rows 7 74 164 280 49 160 64 128 256), losses := [] }

theorem u1401 : Upper (D 8) (R 8) [6,72,160,272,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1402 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 296 49 33 208 208 464), lower := (rows 7 74 164 296 49 33 64 128 256), losses := [] }

theorem u1402 : Upper (D 8) (R 8) [6,72,160,288,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1402 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1403 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 74 164 296 49 48 193 193 449), lower := (rows 7 74 164 296 49 48 64 128 256), losses := [] }

theorem u1403 : Upper (D 8) (R 8) [6,72,160,288,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1403 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1404 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 132, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 296 49 96 209 145 401), lower := (rows 7 74 164 296 49 96 64 128 256), losses := [] }

theorem u1404 : Upper (D 8) (R 8) [6,72,160,288,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1404 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1405 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 296 49 160 81 209 337), lower := (rows 7 74 164 296 49 160 64 128 256), losses := [] }

theorem u1405 : Upper (D 8) (R 8) [6,72,160,288,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1406 : Route 9 := (fun mask => (mask,id))

def c1406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1406 : Upper (D 8) (R 8) [6,72,160,288,96,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,96,1] 13 (by decide) (choices 1) [1,16,128] r1406 c1406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u153
  · exact u154
  · exact u155

def b1407 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 74 164 296 112 48 193 129 385), lower := (rows 7 74 164 296 112 48 64 128 256), losses := [] }

theorem u1407 : Upper (D 8) (R 8) [6,72,160,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1407 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1408 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 296 112 160 81 145 273), lower := (rows 7 74 164 296 112 160 64 128 256), losses := [] }

theorem u1408 : Upper (D 8) (R 8) [6,72,160,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1409 : Route 9 := (fun mask => (mask,id))

def c1409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1409 : Upper (D 8) (R 8) [6,72,160,288,192,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,192,1] 13 (by decide) (choices 1) [1,16,32] r1409 c1409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u156
  · exact u157
  · exact u158

def b1410 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 74 164 296 208 48 97 161 289), lower := (rows 7 74 164 296 208 48 64 128 256), losses := [] }

theorem u1410 : Upper (D 8) (R 8) [6,72,160,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1410 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1411 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 168 112 33 240 176 432), lower := (rows 7 74 261 168 112 33 64 128 256), losses := [] }

theorem u1411 : Upper (D 8) (R 8) [6,72,257,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1411 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1412 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 74 261 168 112 48 225 161 417), lower := (rows 7 74 261 168 112 48 64 128 256), losses := [] }

theorem u1412 : Upper (D 8) (R 8) [6,72,257,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1412 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1413 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 261 168 112 160 113 177 305), lower := (rows 7 74 261 168 112 160 64 128 256), losses := [] }

theorem u1413 : Upper (D 8) (R 8) [6,72,257,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1414 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 261 168 208 33 112 176 304), lower := (rows 7 74 261 168 208 33 64 128 256), losses := [] }

theorem u1414 : Upper (D 8) (R 8) [6,72,257,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1414 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1415 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 74 261 168 208 48 97 161 289), lower := (rows 7 74 261 168 208 48 64 128 256), losses := [] }

theorem u1415 : Upper (D 8) (R 8) [6,72,257,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1415 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1416 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 276 41 176 33 224 224 480), lower := (rows 7 74 276 41 176 33 64 128 256), losses := [] }

theorem u1416 : Upper (D 8) (R 8) [6,72,272,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1417 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 276 41 176 96 225 161 417), lower := (rows 7 74 276 41 176 96 64 128 256), losses := [] }

theorem u1417 : Upper (D 8) (R 8) [6,72,272,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1417 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1418 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 276 41 176 160 97 225 353), lower := (rows 7 74 276 41 176 160 64 128 256), losses := [] }

theorem u1418 : Upper (D 8) (R 8) [6,72,272,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1419 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 276 168 49 33 224 224 480), lower := (rows 7 74 276 168 49 33 64 128 256), losses := [] }

theorem u1419 : Upper (D 8) (R 8) [6,72,272,160,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1419 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1420 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 276 168 49 96 225 161 417), lower := (rows 7 74 276 168 49 96 64 128 256), losses := [] }

theorem u1420 : Upper (D 8) (R 8) [6,72,272,160,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1420 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1421 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 276 168 49 160 97 225 353), lower := (rows 7 74 276 168 49 160 64 128 256), losses := [] }

theorem u1421 : Upper (D 8) (R 8) [6,72,272,160,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1422 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 292 25 176 33 224 224 480), lower := (rows 7 74 292 25 176 33 64 128 256), losses := [] }

theorem u1422 : Upper (D 8) (R 8) [6,72,288,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1422 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1423 : Route 9 := (fun mask => (mask,id))

def c1423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1423 : Upper (D 8) (R 8) [6,72,288,17,160,64] 13 := by
  apply FastRouting.sound _ _ [6,72,288,17,160,64] 13 (by decide) (choices 1) [1,32,128] r1423 c1423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u159
  · exact u160
  · exact u161

def b1424 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 25 176 160 97 225 353), lower := (rows 7 74 292 25 176 160 64 128 256), losses := [] }

theorem u1424 : Upper (D 8) (R 8) [6,72,288,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1425 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 41 112 33 208 144 400), lower := (rows 7 74 292 41 112 33 64 128 256), losses := [] }

theorem u1425 : Upper (D 8) (R 8) [6,72,288,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1425 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1426 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 74 292 41 112 48 193 129 385), lower := (rows 7 74 292 41 112 48 64 128 256), losses := [] }

theorem u1426 : Upper (D 8) (R 8) [6,72,288,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1426 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1427 : Route 9 := (fun mask => (mask,id))

def c1427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1427 : Upper (D 8) (R 8) [6,72,288,33,96,128] 13 := by
  apply FastRouting.sound _ _ [6,72,288,33,96,128] 13 (by decide) (choices 1) [1,16,128] r1427 c1427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u162
  · exact u163
  · exact u164

def b1428 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 41 176 33 208 208 464), lower := (rows 7 74 292 41 176 33 64 128 256), losses := [] }

theorem u1428 : Upper (D 8) (R 8) [6,72,288,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1429 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 74 292 41 176 48 193 193 449), lower := (rows 7 74 292 41 176 48 64 128 256), losses := [] }

theorem u1429 : Upper (D 8) (R 8) [6,72,288,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1429 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1430 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 292 41 176 96 209 145 401), lower := (rows 7 74 292 41 176 96 64 128 256), losses := [] }

theorem u1430 : Upper (D 8) (R 8) [6,72,288,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1431 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 41 176 160 81 209 337), lower := (rows 7 74 292 41 176 160 64 128 256), losses := [] }

theorem u1431 : Upper (D 8) (R 8) [6,72,288,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1432 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 41 208 33 240 176 432), lower := (rows 7 74 292 41 208 33 64 128 256), losses := [] }

theorem u1432 : Upper (D 8) (R 8) [6,72,288,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1433 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 74 292 41 208 48 225 161 417), lower := (rows 7 74 292 41 208 48 64 128 256), losses := [] }

theorem u1433 : Upper (D 8) (R 8) [6,72,288,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1433 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1434 : Route 9 := (fun mask => (mask,id))

def c1434 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1434 : Upper (D 8) (R 8) [6,72,288,33,192,128] 13 := by
  apply FastRouting.sound _ _ [6,72,288,33,192,128] 13 (by decide) (choices 1) [1,16,32] r1434 c1434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u165
  · exact u166
  · exact u167

def b1435 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 56 145 33 224 224 480), lower := (rows 7 74 292 56 145 33 64 128 256), losses := [] }

theorem u1435 : Upper (D 8) (R 8) [6,72,288,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1436 : Route 9 := (fun mask => (mask,id))

def c1436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1436 : Upper (D 8) (R 8) [6,72,288,48,129,64] 13 := by
  apply FastRouting.sound _ _ [6,72,288,48,129,64] 13 (by decide) (choices 1) [1,32,128] r1436 c1436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u168
  · exact u169
  · exact u170

def b1437 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 56 145 160 97 225 353), lower := (rows 7 74 292 56 145 160 64 128 256), losses := [] }

theorem u1437 : Upper (D 8) (R 8) [6,72,288,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1438 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 292 137 112 33 240 176 432), lower := (rows 7 74 292 137 112 33 64 128 256), losses := [] }

theorem u1438 : Upper (D 8) (R 8) [6,72,288,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1439 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 74 292 137 112 48 225 161 417), lower := (rows 7 74 292 137 112 48 64 128 256), losses := [] }

theorem u1439 : Upper (D 8) (R 8) [6,72,288,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1439 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1439
end Delivery.IrregularNine14.P08
