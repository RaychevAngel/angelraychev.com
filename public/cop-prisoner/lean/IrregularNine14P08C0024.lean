import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0002
import IrregularNine14P08C0003

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1440 : PairBound 9 := { available := 49, camps := [], pairs := [(4,0)], upper := (rows 7 74 292 137 112 160 113 177 305), lower := (rows 7 74 292 137 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 168 64 128 256), good := (rows 22 122 292 168 112 160 64 160 256) }] }

theorem u1440 : Upper (D 8) (R 8) [6,72,288,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1441 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 292 137 176 33 112 240 368), lower := (rows 7 74 292 137 176 33 64 128 256), losses := [] }

theorem u1441 : Upper (D 8) (R 8) [6,72,288,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1442 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 74 292 137 176 48 97 225 353), lower := (rows 7 74 292 137 176 48 64 128 256), losses := [] }

theorem u1442 : Upper (D 8) (R 8) [6,72,288,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1442 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1443 : Route 9 := (fun mask => (mask,id))

def c1443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1443 : Upper (D 8) (R 8) [6,72,288,129,160,64] 13 := by
  apply FastRouting.sound _ _ [6,72,288,129,160,64] 13 (by decide) (choices 1) [1,16,32] r1443 c1443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u171
  · exact u172
  · exact u173

def b1444 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 292 137 208 33 112 176 304), lower := (rows 7 74 292 137 208 33 64 128 256), losses := [] }

theorem u1444 : Upper (D 8) (R 8) [6,72,288,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1445 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 74 292 137 208 48 97 161 289), lower := (rows 7 74 292 137 208 48 64 128 256), losses := [] }

theorem u1445 : Upper (D 8) (R 8) [6,72,288,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1445 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1446 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 152 49 33 224 224 480), lower := (rows 7 74 292 152 49 33 64 128 256), losses := [] }

theorem u1446 : Upper (D 8) (R 8) [6,72,288,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1447 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 292 152 49 96 225 161 417), lower := (rows 7 74 292 152 49 96 64 128 256), losses := [] }

theorem u1447 : Upper (D 8) (R 8) [6,72,288,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1447 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1448 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 324, targets := 128 }], pairs := [(2,7)], upper := (rows 7 74 292 152 49 160 97 225 353), lower := (rows 7 74 292 152 49 160 64 128 256), losses := [] }

theorem u1448 : Upper (D 8) (R 8) [6,72,288,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1448 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1449 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 292 168 49 33 208 208 464), lower := (rows 7 74 292 168 49 33 64 128 256), losses := [] }

theorem u1449 : Upper (D 8) (R 8) [6,72,288,160,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1450 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 74 292 168 49 48 193 193 449), lower := (rows 7 74 292 168 49 48 64 128 256), losses := [] }

theorem u1450 : Upper (D 8) (R 8) [6,72,288,160,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1450 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1451 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 292 168 49 96 209 145 401), lower := (rows 7 74 292 168 49 96 64 128 256), losses := [] }

theorem u1451 : Upper (D 8) (R 8) [6,72,288,160,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1452 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 168 49 160 81 209 337), lower := (rows 7 74 292 168 49 160 64 128 256), losses := [] }

theorem u1452 : Upper (D 8) (R 8) [6,72,288,160,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1452 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1453 : Route 9 := (fun mask => (mask,id))

def c1453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1453 : Upper (D 8) (R 8) [6,72,288,160,96,1] 13 := by
  apply FastRouting.sound _ _ [6,72,288,160,96,1] 13 (by decide) (choices 1) [1,16,128] r1453 c1453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u174
  · exact u175
  · exact u176

def b1454 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 74 292 168 112 48 193 129 385), lower := (rows 7 74 292 168 112 48 64 128 256), losses := [] }

theorem u1454 : Upper (D 8) (R 8) [6,72,288,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1454 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1455 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 292 168 112 160 81 145 273), lower := (rows 7 74 292 168 112 160 64 128 256), losses := [] }

theorem u1455 : Upper (D 8) (R 8) [6,72,288,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1456 : Route 9 := (fun mask => (mask,id))

def c1456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1456 : Upper (D 8) (R 8) [6,72,288,160,192,1] 13 := by
  apply FastRouting.sound _ _ [6,72,288,160,192,1] 13 (by decide) (choices 1) [1,16,32] r1456 c1456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u177
  · exact u178
  · exact u179

def b1457 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 74 292 168 208 48 97 161 289), lower := (rows 7 74 292 168 208 48 64 128 256), losses := [] }

theorem u1457 : Upper (D 8) (R 8) [6,72,288,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1457 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1458 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 388 41 112 33 240 176 432), lower := (rows 7 74 388 41 112 33 64 128 256), losses := [] }

theorem u1458 : Upper (D 8) (R 8) [6,72,384,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1459 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 74 388 41 112 48 225 161 417), lower := (rows 7 74 388 41 112 48 64 128 256), losses := [] }

theorem u1459 : Upper (D 8) (R 8) [6,72,384,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1459 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1460 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 82, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 388 41 112 160 113 177 305), lower := (rows 7 74 388 41 112 160 64 128 256), losses := [] }

theorem u1460 : Upper (D 8) (R 8) [6,72,384,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1461 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 388 41 176 33 112 240 368), lower := (rows 7 74 388 41 176 33 64 128 256), losses := [] }

theorem u1461 : Upper (D 8) (R 8) [6,72,384,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1462 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 74 388 41 176 48 97 225 353), lower := (rows 7 74 388 41 176 48 64 128 256), losses := [] }

theorem u1462 : Upper (D 8) (R 8) [6,72,384,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1462 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1463 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 388 41 176 96 113 177 305), lower := (rows 7 74 388 41 176 96 64 128 256), losses := [] }

theorem u1463 : Upper (D 8) (R 8) [6,72,384,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1464 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 388 41 208 33 112 176 304), lower := (rows 7 74 388 41 208 33 64 128 256), losses := [] }

theorem u1464 : Upper (D 8) (R 8) [6,72,384,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1465 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 74 388 41 208 48 97 161 289), lower := (rows 7 74 388 41 208 48 64 128 256), losses := [] }

theorem u1465 : Upper (D 8) (R 8) [6,72,384,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1465 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1466 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 164 25 56 33 448 448 448), lower := (rows 7 98 164 25 56 33 64 128 256), losses := [] }

theorem u1466 : Upper (D 8) (R 8) [6,96,160,17,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1467 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 25 56 96 449 385 385), lower := (rows 7 98 164 25 56 96 64 128 256), losses := [] }

theorem u1467 : Upper (D 8) (R 8) [6,96,160,17,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1468 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 98 164 25 56 288 193 193 449), lower := (rows 7 98 164 25 56 288 64 128 256), losses := [] }

theorem u1468 : Upper (D 8) (R 8) [6,96,160,17,40,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1468 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1469 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 164 25 280 33 224 224 480), lower := (rows 7 98 164 25 280 33 64 128 256), losses := [] }

theorem u1469 : Upper (D 8) (R 8) [6,96,160,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1470 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 25 280 96 225 161 417), lower := (rows 7 98 164 25 280 96 64 128 256), losses := [] }

theorem u1470 : Upper (D 8) (R 8) [6,96,160,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1471 : Route 9 := (fun mask => (mask,id))

def c1471 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1471 : Upper (D 8) (R 8) [6,96,160,17,288,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,288,1] 13 (by decide) (choices 1) [8,128] r1471 c1471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u180
  · exact u181

def b1472 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 98 164 25 304 40 193 193 449), lower := (rows 7 98 164 25 304 40 64 128 256), losses := [] }

theorem u1472 : Upper (D 8) (R 8) [6,96,160,17,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1472 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1473 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 25 304 96 201 137 393), lower := (rows 7 98 164 25 304 96 64 128 256), losses := [] }

theorem u1473 : Upper (D 8) (R 8) [6,96,160,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1474 : Route 9 := (fun mask => (mask,id))

def c1474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u1474 : Upper (D 8) (R 8) [6,96,160,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48,192,1] 13 (by decide) (choices 1) [1,8,256] r1474 c1474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u182
  · exact u183
  · exact u184

def b1475 : PairBound 9 := { available := 257, camps := [], pairs := [], upper := (rows 7 98 164 56 208 40 321 385 257), lower := (rows 7 98 164 56 208 40 64 128 256), losses := [] }

theorem u1475 : Upper (D 8) (R 8) [6,96,160,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1475 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1476 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 98 164 56 208 288 73 137 265), lower := (rows 7 98 164 56 208 288 64 128 256), losses := [] }

theorem u1476 : Upper (D 8) (R 8) [6,96,160,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1476 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1477 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 164 56 273 33 200 200 456), lower := (rows 7 98 164 56 273 33 64 128 256), losses := [] }

theorem u1477 : Upper (D 8) (R 8) [6,96,160,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1478 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 98 164 56 273 40 193 193 449), lower := (rows 7 98 164 56 273 40 64 128 256), losses := [] }

theorem u1478 : Upper (D 8) (R 8) [6,96,160,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1478 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1479 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 56 273 96 201 137 393), lower := (rows 7 98 164 56 273 96 64 128 256), losses := [] }

theorem u1479 : Upper (D 8) (R 8) [6,96,160,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1480 : PairBound 9 := { available := 193, camps := [], pairs := [(4,5)], upper := (rows 7 98 164 56 280 33 193 193 449), lower := (rows 7 98 164 56 280 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 24 0 97 161 289), good := (rows 455 450 452 472 280 449 64 128 256) }] }

theorem u1480 : Upper (D 8) (R 8) [6,96,160,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1481 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 164 56 280 96 193 129 385), lower := (rows 7 98 164 56 280 96 64 128 256), losses := [] }

theorem u1481 : Upper (D 8) (R 8) [6,96,160,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1482 : Route 9 := (fun mask => (mask,id))

def c1482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1482 : Upper (D 8) (R 8) [6,96,160,48,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,48,320,1] 13 (by decide) (choices 1) [1,8,128] r1482 c1482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u185
  · exact u186
  · exact u187

def b1483 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 98 164 56 336 40 193 129 385), lower := (rows 7 98 164 56 336 40 64 128 256), losses := [] }

theorem u1483 : Upper (D 8) (R 8) [6,96,160,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1483 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1484 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 164 56 336 160 73 137 265), lower := (rows 7 98 164 56 336 160 64 128 256), losses := [] }

theorem u1484 : Upper (D 8) (R 8) [6,96,160,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1485 : PairBound 9 := { available := 168, camps := [], pairs := [(2,6)], upper := (rows 7 98 164 88 273 33 232 168 424), lower := (rows 7 98 164 88 273 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 49 0 136 264), good := (rows 39 34 164 444 305 33 0 128 256) }] }

theorem u1485 : Upper (D 8) (R 8) [6,96,160,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1486 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 98 164 88 273 40 225 161 417), lower := (rows 7 98 164 88 273 40 64 128 256), losses := [] }

theorem u1486 : Upper (D 8) (R 8) [6,96,160,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1486 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1487 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 164 88 273 160 105 169 297), lower := (rows 7 98 164 88 273 160 64 128 256), losses := [] }

theorem u1487 : Upper (D 8) (R 8) [6,96,160,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1488 : Route 9 := (fun mask => (mask,id))

def c1488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1488 : Upper (D 8) (R 8) [6,96,160,80,288,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,288,1] 13 (by decide) (choices 1) [1,8,128] r1488 c1488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u188
  · exact u189
  · exact u190

def b1489 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 98 164 88 304 40 193 129 385), lower := (rows 7 98 164 88 304 40 64 128 256), losses := [] }

theorem u1489 : Upper (D 8) (R 8) [6,96,160,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1489 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1490 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 164 88 304 160 73 137 265), lower := (rows 7 98 164 88 304 160 64 128 256), losses := [] }

theorem u1490 : Upper (D 8) (R 8) [6,96,160,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1491 : Route 9 := (fun mask => (mask,id))

def c1491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1491 : Upper (D 8) (R 8) [6,96,160,80,384,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,384,1] 13 (by decide) (choices 1) [1,8,32] r1491 c1491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u191
  · exact u192
  · exact u193

def b1492 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 98 164 88 400 40 97 161 289), lower := (rows 7 98 164 88 400 40 64 128 256), losses := [] }

theorem u1492 : Upper (D 8) (R 8) [6,96,160,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1492 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1493 : Route 9 := (fun mask => (mask,id))

def c1493 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1493 : Upper (D 8) (R 8) [6,96,160,192,257,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,257,1] 13 (by decide) (choices 1) [8,16,32] r1493 c1493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u194
  · exact u195
  · exact u196

def b1494 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 98 164 200 273 40 113 177 305), lower := (rows 7 98 164 200 273 40 64 128 256), losses := [] }

theorem u1494 : Upper (D 8) (R 8) [6,96,160,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1494 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1495 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 98 164 200 273 48 105 169 297), lower := (rows 7 98 164 200 273 48 64 128 256), losses := [] }

theorem u1495 : Upper (D 8) (R 8) [6,96,160,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1495 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1496 : Route 9 := (fun mask => (mask,id))

def c1496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1496 : Upper (D 8) (R 8) [6,96,160,192,264,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,264,1] 13 (by decide) (choices 1) [1,16,32] r1496 c1496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u197
  · exact u198
  · exact u199

def b1497 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 98 164 200 280 48 97 161 289), lower := (rows 7 98 164 200 280 48 64 128 256), losses := [] }

theorem u1497 : Upper (D 8) (R 8) [6,96,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1497 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1498 : Route 9 := (fun mask => (mask,id))

def c1498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1498 : Upper (D 8) (R 8) [6,96,160,192,288,1] 13 := by
  apply FastRouting.sound _ _ [6,96,160,192,288,1] 13 (by decide) (choices 1) [1,8,16] r1498 c1498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u200
  · exact u201
  · exact u202

def b1499 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 7 98 164 200 304 40 81 145 273), lower := (rows 7 98 164 200 304 40 64 128 256), losses := [] }

theorem u1499 : Upper (D 8) (R 8) [6,96,160,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1499 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1499
end Delivery.IrregularNine14.P08
