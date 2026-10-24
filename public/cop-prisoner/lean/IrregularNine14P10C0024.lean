import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0008

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1440 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 76 152 304 416 480 416 416), lower := (rows 7 67 76 152 304 32 64 128 256), losses := [] }

theorem u1440 : Upper (D 10) (R 10) [6,65,72,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1440 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1441 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 76 168 304 432 496 432 432), lower := (rows 7 67 76 168 304 32 64 128 256), losses := [] }

theorem u1441 : Upper (D 10) (R 10) [6,65,72,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1441 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1442 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 76 168 400 304 368 432 304), lower := (rows 7 67 76 168 400 32 64 128 256), losses := [] }

theorem u1442 : Upper (D 10) (R 10) [6,65,72,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1442 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1443 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 76 392 176 304 368 432 304), lower := (rows 7 67 76 392 176 32 64 128 256), losses := [] }

theorem u1443 : Upper (D 10) (R 10) [6,65,72,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1443 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1444 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 100 56 152 416 480 416 416), lower := (rows 7 67 100 56 152 32 64 128 256), losses := [] }

theorem u1444 : Upper (D 10) (R 10) [6,65,96,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1444 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1445 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 100 56 400 424 488 424 424), lower := (rows 7 67 100 56 400 32 64 128 256), losses := [] }

theorem u1445 : Upper (D 10) (R 10) [6,65,96,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1445 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1446 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 100 152 280 416 480 416 416), lower := (rows 7 67 100 152 280 32 64 128 256), losses := [] }

theorem u1446 : Upper (D 10) (R 10) [6,65,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1446 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1447 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 100 152 304 424 488 424 424), lower := (rows 7 67 100 152 304 32 64 128 256), losses := [] }

theorem u1447 : Upper (D 10) (R 10) [6,65,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1447 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1448 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 100 168 304 440 472 408 408), lower := (rows 7 67 100 168 304 32 64 128 256), losses := [] }

theorem u1448 : Upper (D 10) (R 10) [6,65,96,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1448 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1449 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 100 168 400 312 376 440 312), lower := (rows 7 67 100 168 400 32 64 128 256), losses := [] }

theorem u1449 : Upper (D 10) (R 10) [6,65,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1449 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1450 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 140 56 112 416 480 416 416), lower := (rows 7 67 140 56 112 32 64 128 256), losses := [] }

theorem u1450 : Upper (D 10) (R 10) [6,65,136,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1450 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1451 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 12, targets := 320 }], pairs := [(2,6),(2,8)], upper := (rows 7 67 140 56 176 352 352 480 352), lower := (rows 7 67 140 56 176 32 64 128 256), losses := [] }

theorem u1451 : Upper (D 10) (R 10) [6,65,136,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1451 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1452 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 140 56 208 288 352 416 288), lower := (rows 7 67 140 56 208 32 64 128 256), losses := [] }

theorem u1452 : Upper (D 10) (R 10) [6,65,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1452 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1453 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 67 140 56 304 480 480 480 480), lower := (rows 7 67 140 56 304 32 64 128 256), losses := [] }

theorem u1453 : Upper (D 10) (R 10) [6,65,136,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1453 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1454 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 140 56 336 416 480 416 416), lower := (rows 7 67 140 56 336 32 64 128 256), losses := [] }

theorem u1454 : Upper (D 10) (R 10) [6,65,136,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1454 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1455 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 140 56 400 352 352 480 352), lower := (rows 7 67 140 56 400 32 64 128 256), losses := [] }

theorem u1455 : Upper (D 10) (R 10) [6,65,136,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1455 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1456 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 140 88 176 288 352 416 288), lower := (rows 7 67 140 88 176 32 64 128 256), losses := [] }

theorem u1456 : Upper (D 10) (R 10) [6,65,136,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1456 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1457 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 140 88 304 416 480 416 416), lower := (rows 7 67 140 88 304 32 64 128 256), losses := [] }

theorem u1457 : Upper (D 10) (R 10) [6,65,136,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1457 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1458 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 140 88 400 288 352 416 288), lower := (rows 7 67 140 88 400 32 64 128 256), losses := [] }

theorem u1458 : Upper (D 10) (R 10) [6,65,136,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1458 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1459 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 140 104 176 304 368 432 304), lower := (rows 7 67 140 104 176 32 64 128 256), losses := [] }

theorem u1459 : Upper (D 10) (R 10) [6,65,136,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1459 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1460 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 140 104 304 432 496 432 432), lower := (rows 7 67 140 104 304 32 64 128 256), losses := [] }

theorem u1460 : Upper (D 10) (R 10) [6,65,136,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1460 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1461 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 140 104 400 304 368 432 304), lower := (rows 7 67 140 104 400 32 64 128 256), losses := [] }

theorem u1461 : Upper (D 10) (R 10) [6,65,136,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1461 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1462 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 140 152 304 352 352 480 352), lower := (rows 7 67 140 152 304 32 64 128 256), losses := [] }

theorem u1462 : Upper (D 10) (R 10) [6,65,136,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1462 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1463 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 140 168 304 368 368 496 368), lower := (rows 7 67 140 168 304 32 64 128 256), losses := [] }

theorem u1463 : Upper (D 10) (R 10) [6,65,136,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1463 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1464 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 7, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 67 140 200 304 304 368 432 304), lower := (rows 7 67 140 200 304 32 64 128 256), losses := [] }

theorem u1464 : Upper (D 10) (R 10) [6,65,136,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1464 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1465 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 140 280 112 416 480 416 416), lower := (rows 7 67 140 280 112 32 64 128 256), losses := [] }

theorem u1465 : Upper (D 10) (R 10) [6,65,136,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1465 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1466 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 140 280 176 352 352 480 352), lower := (rows 7 67 140 280 176 32 64 128 256), losses := [] }

theorem u1466 : Upper (D 10) (R 10) [6,65,136,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1466 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1467 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 140 280 208 288 352 416 288), lower := (rows 7 67 140 280 208 32 64 128 256), losses := [] }

theorem u1467 : Upper (D 10) (R 10) [6,65,136,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1467 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1468 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 67 140 280 304 224 224 224 480), lower := (rows 7 67 140 280 304 32 64 128 256), losses := [] }

theorem u1468 : Upper (D 10) (R 10) [6,65,136,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1468 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1469 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 67 140 280 336 160 224 160 416), lower := (rows 7 67 140 280 336 32 64 128 256), losses := [] }

theorem u1469 : Upper (D 10) (R 10) [6,65,136,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1469 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1470 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 12, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 7 67 140 280 400 96 96 224 352), lower := (rows 7 67 140 280 400 32 64 128 256), losses := [] }

theorem u1470 : Upper (D 10) (R 10) [6,65,136,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1470 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1471 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 140 296 112 432 496 432 432), lower := (rows 7 67 140 296 112 32 64 128 256), losses := [] }

theorem u1471 : Upper (D 10) (R 10) [6,65,136,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1471 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1472 : Route 9 := (fun mask => (mask,id))

def c1472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1472 : Upper (D 10) (R 10) [6,65,136,288,160] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,160] 13 (by decide) (choices 1) [16,64,256] r1472 c1472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u513
  · exact u514
  · exact u515

def b1473 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 300, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 140 296 208 304 368 432 304), lower := (rows 7 67 140 296 208 32 64 128 256), losses := [] }

theorem u1473 : Upper (D 10) (R 10) [6,65,136,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1473 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1474 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 7 67 140 296 304 240 240 240 496), lower := (rows 7 67 140 296 304 32 64 128 256), losses := [] }

theorem u1474 : Upper (D 10) (R 10) [6,65,136,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1474 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1475 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 140 296 336 176 240 176 432), lower := (rows 7 67 140 296 336 32 64 128 256), losses := [] }

theorem u1475 : Upper (D 10) (R 10) [6,65,136,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1475 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1476 : Route 9 := (fun mask => (mask,id))

def c1476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1476 : Upper (D 10) (R 10) [6,65,136,288,384] 13 := by
  apply FastRouting.sound _ _ [6,65,136,288,384] 13 (by decide) (choices 1) [16,64] r1476 c1476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u516
  · exact u517

def b1477 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 140 328 176 304 368 432 304), lower := (rows 7 67 140 328 176 32 64 128 256), losses := [] }

theorem u1477 : Upper (D 10) (R 10) [6,65,136,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1477 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1478 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 140 328 304 176 240 176 432), lower := (rows 7 67 140 328 304 32 64 128 256), losses := [] }

theorem u1478 : Upper (D 10) (R 10) [6,65,136,320,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1478 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1479 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 140 328 400 48 112 176 304), lower := (rows 7 67 140 328 400 32 64 128 256), losses := [] }

theorem u1479 : Upper (D 10) (R 10) [6,65,136,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1479 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1480 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 140 392 304 112 112 240 368), lower := (rows 7 67 140 392 304 32 64 128 256), losses := [] }

theorem u1480 : Upper (D 10) (R 10) [6,65,136,384,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1480 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1481 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 24, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 67 164 56 56 480 448 448 448), lower := (rows 7 67 164 56 56 32 64 128 256), losses := [] }

theorem u1481 : Upper (D 10) (R 10) [6,65,160,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1481 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1482 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 67 164 56 88 416 480 416 416), lower := (rows 7 67 164 56 88 32 64 128 256), losses := [] }

theorem u1482 : Upper (D 10) (R 10) [6,65,160,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1482 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1483 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 164 56 112 424 456 392 392), lower := (rows 7 67 164 56 112 32 64 128 256), losses := [] }

theorem u1483 : Upper (D 10) (R 10) [6,65,160,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1483 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1484 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 24, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 67 164 56 152 352 352 480 352), lower := (rows 7 67 164 56 152 32 64 128 256), losses := [] }

theorem u1484 : Upper (D 10) (R 10) [6,65,160,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1484 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1485 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 24, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 67 164 56 176 360 328 456 328), lower := (rows 7 67 164 56 176 32 64 128 256), losses := [] }

theorem u1485 : Upper (D 10) (R 10) [6,65,160,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1485 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1486 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 300, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 164 56 208 296 360 424 296), lower := (rows 7 67 164 56 208 32 64 128 256), losses := [] }

theorem u1486 : Upper (D 10) (R 10) [6,65,160,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1486 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1487 : Route 9 := (fun mask => (mask,id))

def c1487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1487 : Upper (D 10) (R 10) [6,65,160,48,264] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,264] 13 (by decide) (choices 1) [64,128,256] r1487 c1487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u518
  · exact u519
  · exact u520

def b1488 : PairBound 9 := { available := 456, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 67 164 56 304 488 456 456 456), lower := (rows 7 67 164 56 304 32 64 128 256), losses := [] }

theorem u1488 : Upper (D 10) (R 10) [6,65,160,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1488 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1489 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 164 56 336 424 488 424 424), lower := (rows 7 67 164 56 336 32 64 128 256), losses := [] }

theorem u1489 : Upper (D 10) (R 10) [6,65,160,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1489 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1490 : Route 9 := (fun mask => (mask,id))

def c1490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1490 : Upper (D 10) (R 10) [6,65,160,48,384] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,384] 13 (by decide) (choices 1) [8,64,256] r1490 c1490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u521
  · exact u522
  · exact u523

def b1491 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 67 164 88 152 288 352 416 288), lower := (rows 7 67 164 88 152 32 64 128 256), losses := [] }

theorem u1491 : Upper (D 10) (R 10) [6,65,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1491 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1492 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 67 164 88 280 416 480 416 416), lower := (rows 7 67 164 88 280 32 64 128 256), losses := [] }

theorem u1492 : Upper (D 10) (R 10) [6,65,160,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1492 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1493 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 88 304 424 488 424 424), lower := (rows 7 67 164 88 304 32 64 128 256), losses := [] }

theorem u1493 : Upper (D 10) (R 10) [6,65,160,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1493 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1494 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 88 400 296 360 424 296), lower := (rows 7 67 164 88 400 32 64 128 256), losses := [] }

theorem u1494 : Upper (D 10) (R 10) [6,65,160,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1494 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1495 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 104 152 304 368 432 304), lower := (rows 7 67 164 104 152 32 64 128 256), losses := [] }

theorem u1495 : Upper (D 10) (R 10) [6,65,160,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1495 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1496 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 104 280 432 496 432 432), lower := (rows 7 67 164 104 280 32 64 128 256), losses := [] }

theorem u1496 : Upper (D 10) (R 10) [6,65,160,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1496 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1497 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 104 304 440 472 408 408), lower := (rows 7 67 164 104 304 32 64 128 256), losses := [] }

theorem u1497 : Upper (D 10) (R 10) [6,65,160,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1497 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1498 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 104 400 312 376 440 312), lower := (rows 7 67 164 104 400 32 64 128 256), losses := [] }

theorem u1498 : Upper (D 10) (R 10) [6,65,160,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1498 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1499 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 164 152 280 352 352 480 352), lower := (rows 7 67 164 152 280 32 64 128 256), losses := [] }

theorem u1499 : Upper (D 10) (R 10) [6,65,160,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1499 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1499
end Delivery.IrregularNine14.P10
