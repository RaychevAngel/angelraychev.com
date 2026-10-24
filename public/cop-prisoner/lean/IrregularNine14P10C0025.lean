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

def r1500 : Route 9 := (fun mask => (mask,id))

def c1500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1500 : Upper (D 10) (R 10) [6,65,160,144,288] 13 := by
  apply FastRouting.sound _ _ [6,65,160,144,288] 13 (by decide) (choices 1) [8,64,256] r1500 c1500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u524
  · exact u525
  · exact u526

def b1501 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 164 152 336 296 360 424 296), lower := (rows 7 67 164 152 336 32 64 128 256), losses := [] }

theorem u1501 : Upper (D 10) (R 10) [6,65,160,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1501 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1502 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 67 164 168 280 368 368 496 368), lower := (rows 7 67 164 168 280 32 64 128 256), losses := [] }

theorem u1502 : Upper (D 10) (R 10) [6,65,160,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1502 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1503 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 67 164 168 304 376 344 472 344), lower := (rows 7 67 164 168 304 32 64 128 256), losses := [] }

theorem u1503 : Upper (D 10) (R 10) [6,65,160,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1503 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1504 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 200 280 304 368 432 304), lower := (rows 7 67 164 200 280 32 64 128 256), losses := [] }

theorem u1504 : Upper (D 10) (R 10) [6,65,160,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1504 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1505 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 308, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 200 304 312 376 440 312), lower := (rows 7 67 164 200 304 32 64 128 256), losses := [] }

theorem u1505 : Upper (D 10) (R 10) [6,65,160,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1505 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1506 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 24, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 67 164 280 280 224 224 224 480), lower := (rows 7 67 164 280 280 32 64 128 256), losses := [] }

theorem u1506 : Upper (D 10) (R 10) [6,65,160,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1506 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1507 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 67 164 280 304 232 232 232 488), lower := (rows 7 67 164 280 304 32 64 128 256), losses := [] }

theorem u1507 : Upper (D 10) (R 10) [6,65,160,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1507 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1508 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 67 164 280 336 168 232 168 424), lower := (rows 7 67 164 280 336 32 64 128 256), losses := [] }

theorem u1508 : Upper (D 10) (R 10) [6,65,160,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1508 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1509 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 67 164 280 400 104 104 232 360), lower := (rows 7 67 164 280 400 32 64 128 256), losses := [] }

theorem u1509 : Upper (D 10) (R 10) [6,65,160,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1509 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1510 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 7 67 164 296 304 248 216 216 472), lower := (rows 7 67 164 296 304 32 64 128 256), losses := [] }

theorem u1510 : Upper (D 10) (R 10) [6,65,160,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1510 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1511 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 164 296 336 184 248 184 440), lower := (rows 7 67 164 296 336 32 64 128 256), losses := [] }

theorem u1511 : Upper (D 10) (R 10) [6,65,160,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1511 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1512 : Route 9 := (fun mask => (mask,id))

def c1512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1512 : Upper (D 10) (R 10) [6,65,160,288,384] 13 := by
  apply FastRouting.sound _ _ [6,65,160,288,384] 13 (by decide) (choices 1) [8,16,64] r1512 c1512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u527
  · exact u528
  · exact u529

def b1513 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 180, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 164 328 400 56 120 184 312), lower := (rows 7 67 164 328 400 32 64 128 256), losses := [] }

theorem u1513 : Upper (D 10) (R 10) [6,65,160,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1513 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1514 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 3, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 67 196 56 152 288 352 416 288), lower := (rows 7 67 196 56 152 32 64 128 256), losses := [] }

theorem u1514 : Upper (D 10) (R 10) [6,65,192,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1514 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1515 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 196 56 280 416 480 416 416), lower := (rows 7 67 196 56 280 32 64 128 256), losses := [] }

theorem u1515 : Upper (D 10) (R 10) [6,65,192,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1515 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1516 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 196 56 400 296 360 424 296), lower := (rows 7 67 196 56 400 32 64 128 256), losses := [] }

theorem u1516 : Upper (D 10) (R 10) [6,65,192,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1516 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1517 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 3, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 67 196 152 280 288 352 416 288), lower := (rows 7 67 196 152 280 32 64 128 256), losses := [] }

theorem u1517 : Upper (D 10) (R 10) [6,65,192,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1517 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1518 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 196 152 304 296 360 424 296), lower := (rows 7 67 196 152 304 32 64 128 256), losses := [] }

theorem u1518 : Upper (D 10) (R 10) [6,65,192,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1518 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1519 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 196 168 280 304 368 432 304), lower := (rows 7 67 196 168 280 32 64 128 256), losses := [] }

theorem u1519 : Upper (D 10) (R 10) [6,65,192,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1519 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1520 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 196 168 304 312 376 440 312), lower := (rows 7 67 196 168 304 32 64 128 256), losses := [] }

theorem u1520 : Upper (D 10) (R 10) [6,65,192,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1520 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1521 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 7 67 196 296 400 56 120 184 312), lower := (rows 7 67 196 296 400 32 64 128 256), losses := [] }

theorem u1521 : Upper (D 10) (R 10) [6,65,192,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1521 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1522 : PairBound 9 := { available := 480, camps := [{ cop := 5, region := 24, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 67 388 56 56 480 480 480 480), lower := (rows 7 67 388 56 56 32 64 128 256), losses := [] }

theorem u1522 : Upper (D 10) (R 10) [6,65,384,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1522 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1523 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 67 388 56 88 416 480 416 416), lower := (rows 7 67 388 56 88 32 64 128 256), losses := [] }

theorem u1523 : Upper (D 10) (R 10) [6,65,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1523 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1524 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 388 56 112 424 488 424 424), lower := (rows 7 67 388 56 112 32 64 128 256), losses := [] }

theorem u1524 : Upper (D 10) (R 10) [6,65,384,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1524 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1525 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 388 56 152 352 352 480 352), lower := (rows 7 67 388 56 152 32 64 128 256), losses := [] }

theorem u1525 : Upper (D 10) (R 10) [6,65,384,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1525 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1526 : PairBound 9 := { available := 360, camps := [{ cop := 4, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 67 388 56 176 360 360 488 360), lower := (rows 7 67 388 56 176 32 64 128 256), losses := [] }

theorem u1526 : Upper (D 10) (R 10) [6,65,384,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1526 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1527 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 300, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 388 56 208 296 360 424 296), lower := (rows 7 67 388 56 208 32 64 128 256), losses := [] }

theorem u1527 : Upper (D 10) (R 10) [6,65,384,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1527 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1528 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 67 388 56 400 104 104 232 360), lower := (rows 7 67 388 56 400 32 64 128 256), losses := [] }

theorem u1528 : Upper (D 10) (R 10) [6,65,384,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1528 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1529 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 67 388 88 152 288 352 416 288), lower := (rows 7 67 388 88 152 32 64 128 256), losses := [] }

theorem u1529 : Upper (D 10) (R 10) [6,65,384,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1529 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1530 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 388 88 176 296 360 424 296), lower := (rows 7 67 388 88 176 32 64 128 256), losses := [] }

theorem u1530 : Upper (D 10) (R 10) [6,65,384,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1530 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1531 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 388 104 152 304 368 432 304), lower := (rows 7 67 388 104 152 32 64 128 256), losses := [] }

theorem u1531 : Upper (D 10) (R 10) [6,65,384,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1531 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1532 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 67 388 104 176 312 376 440 312), lower := (rows 7 67 388 104 176 32 64 128 256), losses := [] }

theorem u1532 : Upper (D 10) (R 10) [6,65,384,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1532 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1533 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 24, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 67 388 152 280 96 96 224 352), lower := (rows 7 67 388 152 280 32 64 128 256), losses := [] }

theorem u1533 : Upper (D 10) (R 10) [6,65,384,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1533 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1534 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 368, targets := 128 },{ cop := 4, region := 200, targets := 256 }], pairs := [(3,8),(4,7)], upper := (rows 7 67 388 152 304 104 104 232 360), lower := (rows 7 67 388 152 304 32 64 128 256), losses := [] }

theorem u1534 : Upper (D 10) (R 10) [6,65,384,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1534 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1535 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 388 152 336 40 104 168 296), lower := (rows 7 67 388 152 336 32 64 128 256), losses := [] }

theorem u1535 : Upper (D 10) (R 10) [6,65,384,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1535 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1536 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 336, targets := 128 },{ cop := 4, region := 200, targets := 256 }], pairs := [(3,8),(4,7)], upper := (rows 7 67 388 168 304 120 120 248 376), lower := (rows 7 67 388 168 304 32 64 128 256), losses := [] }

theorem u1536 : Upper (D 10) (R 10) [6,65,384,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1536 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1537 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 172, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 388 168 336 56 120 184 312), lower := (rows 7 67 388 168 336 32 64 128 256), losses := [] }

theorem u1537 : Upper (D 10) (R 10) [6,65,384,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1537 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1538 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 84 41 176 416 480 416 416), lower := (rows 7 74 84 41 176 32 64 128 256), losses := [] }

theorem u1538 : Upper (D 10) (R 10) [6,72,80,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1538 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1539 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 84 41 400 416 480 416 416), lower := (rows 7 74 84 41 400 32 64 128 256), losses := [] }

theorem u1539 : Upper (D 10) (R 10) [6,72,80,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1539 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1540 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 84 137 176 288 352 416 288), lower := (rows 7 74 84 137 176 32 64 128 256), losses := [] }

theorem u1540 : Upper (D 10) (R 10) [6,72,80,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1540 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1541 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 84 137 304 416 480 416 416), lower := (rows 7 74 84 137 304 32 64 128 256), losses := [] }

theorem u1541 : Upper (D 10) (R 10) [6,72,80,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1541 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1542 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 84 137 400 288 352 416 288), lower := (rows 7 74 84 137 400 32 64 128 256), losses := [] }

theorem u1542 : Upper (D 10) (R 10) [6,72,80,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1542 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1543 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 84 168 304 417 481 417 417), lower := (rows 7 74 84 168 304 32 64 128 256), losses := [] }

theorem u1543 : Upper (D 10) (R 10) [6,72,80,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1543 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1544 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 84 168 400 289 353 417 289), lower := (rows 7 74 84 168 400 32 64 128 256), losses := [] }

theorem u1544 : Upper (D 10) (R 10) [6,72,80,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1544 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1545 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 74 100 41 176 432 464 400 400), lower := (rows 7 74 100 41 176 32 64 128 256), losses := [] }

theorem u1545 : Upper (D 10) (R 10) [6,72,96,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1545 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1546 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 74 100 41 400 432 496 432 432), lower := (rows 7 74 100 41 400 32 64 128 256), losses := [] }

theorem u1546 : Upper (D 10) (R 10) [6,72,96,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1546 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1547 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 56 145 416 480 416 416), lower := (rows 7 74 100 56 145 32 64 128 256), losses := [] }

theorem u1547 : Upper (D 10) (R 10) [6,72,96,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1547 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1548 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 56 400 417 481 417 417), lower := (rows 7 74 100 56 400 32 64 128 256), losses := [] }

theorem u1548 : Upper (D 10) (R 10) [6,72,96,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1548 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1549 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 137 176 304 368 432 304), lower := (rows 7 74 100 137 176 32 64 128 256), losses := [] }

theorem u1549 : Upper (D 10) (R 10) [6,72,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1549 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1550 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 137 304 432 496 432 432), lower := (rows 7 74 100 137 304 32 64 128 256), losses := [] }

theorem u1550 : Upper (D 10) (R 10) [6,72,96,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1550 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1551 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 137 400 304 368 432 304), lower := (rows 7 74 100 137 400 32 64 128 256), losses := [] }

theorem u1551 : Upper (D 10) (R 10) [6,72,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1551 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1552 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 152 49 416 480 416 416), lower := (rows 7 74 100 152 49 32 64 128 256), losses := [] }

theorem u1552 : Upper (D 10) (R 10) [6,72,96,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1552 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1553 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 152 273 416 480 416 416), lower := (rows 7 74 100 152 273 32 64 128 256), losses := [] }

theorem u1553 : Upper (D 10) (R 10) [6,72,96,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1553 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1554 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 152 304 417 481 417 417), lower := (rows 7 74 100 152 304 32 64 128 256), losses := [] }

theorem u1554 : Upper (D 10) (R 10) [6,72,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1554 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1555 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 168 49 432 464 400 400), lower := (rows 7 74 100 168 49 32 64 128 256), losses := [] }

theorem u1555 : Upper (D 10) (R 10) [6,72,96,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1555 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1556 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 168 145 304 368 432 304), lower := (rows 7 74 100 168 145 32 64 128 256), losses := [] }

theorem u1556 : Upper (D 10) (R 10) [6,72,96,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1556 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1557 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 168 273 432 496 432 432), lower := (rows 7 74 100 168 273 32 64 128 256), losses := [] }

theorem u1557 : Upper (D 10) (R 10) [6,72,96,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1557 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1558 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 168 304 433 465 401 401), lower := (rows 7 74 100 168 304 32 64 128 256), losses := [] }

theorem u1558 : Upper (D 10) (R 10) [6,72,96,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1558 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1559 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 168 400 305 369 433 305), lower := (rows 7 74 100 168 400 32 64 128 256), losses := [] }

theorem u1559 : Upper (D 10) (R 10) [6,72,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1559 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1559
end Delivery.IrregularNine14.P10
