import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0003

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1500 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 98 164 200 304 48 73 137 265), lower := (rows 7 98 164 200 304 48 64 128 256), losses := [] }

theorem u1500 : Upper (D 8) (R 8) [6,96,160,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1500 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1501 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 56 152 33 224 224 480), lower := (rows 7 98 261 56 152 33 64 128 256), losses := [] }

theorem u1501 : Upper (D 8) (R 8) [6,96,257,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1502 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 261 56 152 96 225 161 417), lower := (rows 7 98 261 56 152 96 64 128 256), losses := [] }

theorem u1502 : Upper (D 8) (R 8) [6,96,257,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1503 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 56 152 160 97 225 353), lower := (rows 7 98 261 56 152 160 64 128 256), losses := [] }

theorem u1503 : Upper (D 8) (R 8) [6,96,257,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1504 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 56 208 33 232 168 424), lower := (rows 7 98 261 56 208 33 64 128 256), losses := [] }

theorem u1504 : Upper (D 8) (R 8) [6,96,257,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1505 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 98 261 56 208 40 225 161 417), lower := (rows 7 98 261 56 208 40 64 128 256), losses := [] }

theorem u1505 : Upper (D 8) (R 8) [6,96,257,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1505 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1506 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 261 56 208 160 105 169 297), lower := (rows 7 98 261 56 208 160 64 128 256), losses := [] }

theorem u1506 : Upper (D 8) (R 8) [6,96,257,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1507 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 88 176 33 232 168 424), lower := (rows 7 98 261 88 176 33 64 128 256), losses := [] }

theorem u1507 : Upper (D 8) (R 8) [6,96,257,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1508 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 98 261 88 176 40 225 161 417), lower := (rows 7 98 261 88 176 40 64 128 256), losses := [] }

theorem u1508 : Upper (D 8) (R 8) [6,96,257,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1508 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1509 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 261 88 176 160 105 169 297), lower := (rows 7 98 261 88 176 160 64 128 256), losses := [] }

theorem u1509 : Upper (D 8) (R 8) [6,96,257,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1510 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 261 168 208 33 120 184 312), lower := (rows 7 98 261 168 208 33 64 128 256), losses := [] }

theorem u1510 : Upper (D 8) (R 8) [6,96,257,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1511 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 98 261 168 208 40 113 177 305), lower := (rows 7 98 261 168 208 40 64 128 256), losses := [] }

theorem u1511 : Upper (D 8) (R 8) [6,96,257,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1511 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1512 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 98 261 168 208 48 105 169 297), lower := (rows 7 98 261 168 208 48 64 128 256), losses := [] }

theorem u1512 : Upper (D 8) (R 8) [6,96,257,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1512 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1513 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 268 25 176 33 224 224 480), lower := (rows 7 98 268 25 176 33 64 128 256), losses := [] }

theorem u1513 : Upper (D 8) (R 8) [6,96,264,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1514 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 268 25 176 96 225 161 417), lower := (rows 7 98 268 25 176 96 64 128 256), losses := [] }

theorem u1514 : Upper (D 8) (R 8) [6,96,264,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1515 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 268 25 176 160 97 225 353), lower := (rows 7 98 268 25 176 160 64 128 256), losses := [] }

theorem u1515 : Upper (D 8) (R 8) [6,96,264,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1516 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 268 41 176 33 208 208 464), lower := (rows 7 98 268 41 176 33 64 128 256), losses := [] }

theorem u1516 : Upper (D 8) (R 8) [6,96,264,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1517 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 98 268 41 176 48 193 193 449), lower := (rows 7 98 268 41 176 48 64 128 256), losses := [] }

theorem u1517 : Upper (D 8) (R 8) [6,96,264,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1517 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1518 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 268 41 176 96 209 145 401), lower := (rows 7 98 268 41 176 96 64 128 256), losses := [] }

theorem u1518 : Upper (D 8) (R 8) [6,96,264,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1519 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 268 41 176 160 81 209 337), lower := (rows 7 98 268 41 176 160 64 128 256), losses := [] }

theorem u1519 : Upper (D 8) (R 8) [6,96,264,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1520 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 268 41 208 33 240 176 432), lower := (rows 7 98 268 41 208 33 64 128 256), losses := [] }

theorem u1520 : Upper (D 8) (R 8) [6,96,264,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1521 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 98 268 41 208 48 225 161 417), lower := (rows 7 98 268 41 208 48 64 128 256), losses := [] }

theorem u1521 : Upper (D 8) (R 8) [6,96,264,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1521 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1522 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 268 41 208 160 113 177 305), lower := (rows 7 98 268 41 208 160 64 128 256), losses := [] }

theorem u1522 : Upper (D 8) (R 8) [6,96,264,33,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1523 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 268 56 145 33 224 224 480), lower := (rows 7 98 268 56 145 33 64 128 256), losses := [] }

theorem u1523 : Upper (D 8) (R 8) [6,96,264,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1524 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 268 56 145 96 225 161 417), lower := (rows 7 98 268 56 145 96 64 128 256), losses := [] }

theorem u1524 : Upper (D 8) (R 8) [6,96,264,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1525 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 268 56 145 160 97 225 353), lower := (rows 7 98 268 56 145 160 64 128 256), losses := [] }

theorem u1525 : Upper (D 8) (R 8) [6,96,264,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1525 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1526 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 7 98 268 56 208 33 225 161 417), lower := (rows 7 98 268 56 208 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 33 0 161 289), good := (rows 423 418 268 444 144 417 0 128 256) }] }

theorem u1526 : Upper (D 8) (R 8) [6,96,264,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1527 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 268 56 208 160 97 161 289), lower := (rows 7 98 268 56 208 160 64 128 256), losses := [] }

theorem u1527 : Upper (D 8) (R 8) [6,96,264,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1528 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 268 137 176 33 112 240 368), lower := (rows 7 98 268 137 176 33 64 128 256), losses := [] }

theorem u1528 : Upper (D 8) (R 8) [6,96,264,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1529 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 98 268 137 176 48 97 225 353), lower := (rows 7 98 268 137 176 48 64 128 256), losses := [] }

theorem u1529 : Upper (D 8) (R 8) [6,96,264,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1529 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1530 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 268 137 176 96 113 177 305), lower := (rows 7 98 268 137 176 96 64 128 256), losses := [] }

theorem u1530 : Upper (D 8) (R 8) [6,96,264,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1531 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 268 137 208 33 112 176 304), lower := (rows 7 98 268 137 208 33 64 128 256), losses := [] }

theorem u1531 : Upper (D 8) (R 8) [6,96,264,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1532 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 98 268 137 208 48 97 161 289), lower := (rows 7 98 268 137 208 48 64 128 256), losses := [] }

theorem u1532 : Upper (D 8) (R 8) [6,96,264,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1532 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1533 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 268 152 49 33 224 224 480), lower := (rows 7 98 268 152 49 33 64 128 256), losses := [] }

theorem u1533 : Upper (D 8) (R 8) [6,96,264,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1534 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 268 152 49 96 225 161 417), lower := (rows 7 98 268 152 49 96 64 128 256), losses := [] }

theorem u1534 : Upper (D 8) (R 8) [6,96,264,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1535 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 268 152 49 160 97 225 353), lower := (rows 7 98 268 152 49 160 64 128 256), losses := [] }

theorem u1535 : Upper (D 8) (R 8) [6,96,264,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1536 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 268 168 49 33 208 208 464), lower := (rows 7 98 268 168 49 33 64 128 256), losses := [] }

theorem u1536 : Upper (D 8) (R 8) [6,96,264,160,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1537 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 98 268 168 49 48 193 193 449), lower := (rows 7 98 268 168 49 48 64 128 256), losses := [] }

theorem u1537 : Upper (D 8) (R 8) [6,96,264,160,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1537 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1538 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 268 168 49 96 209 145 401), lower := (rows 7 98 268 168 49 96 64 128 256), losses := [] }

theorem u1538 : Upper (D 8) (R 8) [6,96,264,160,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1539 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 268 168 49 160 81 209 337), lower := (rows 7 98 268 168 49 160 64 128 256), losses := [] }

theorem u1539 : Upper (D 8) (R 8) [6,96,264,160,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1540 : Route 9 := (fun mask => (mask,id))

def c1540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1540 : Upper (D 8) (R 8) [6,96,264,160,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,264,160,192,1] 13 (by decide) (choices 1) [1,16,32] r1540 c1540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u203
  · exact u204
  · exact u205

def b1541 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 98 268 168 208 48 97 161 289), lower := (rows 7 98 268 168 208 48 64 128 256), losses := [] }

theorem u1541 : Upper (D 8) (R 8) [6,96,264,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1541 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1542 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 292 25 56 33 192 192 448), lower := (rows 7 98 292 25 56 33 64 128 256), losses := [] }

theorem u1542 : Upper (D 8) (R 8) [6,96,288,17,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1543 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 292 25 56 96 193 129 385), lower := (rows 7 98 292 25 56 96 64 128 256), losses := [] }

theorem u1543 : Upper (D 8) (R 8) [6,96,288,17,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1544 : Route 9 := (fun mask => (mask,id))

def c1544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1544 : Upper (D 8) (R 8) [6,96,288,17,40,128] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,40,128] 13 (by decide) (choices 1) [1,128] r1544 c1544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u206
  · exact u207

def b1545 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 292 25 152 33 224 224 480), lower := (rows 7 98 292 25 152 33 64 128 256), losses := [] }

theorem u1545 : Upper (D 8) (R 8) [6,96,288,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1546 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 292 25 152 96 225 161 417), lower := (rows 7 98 292 25 152 96 64 128 256), losses := [] }

theorem u1546 : Upper (D 8) (R 8) [6,96,288,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1547 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 292 25 152 160 97 225 353), lower := (rows 7 98 292 25 152 160 64 128 256), losses := [] }

theorem u1547 : Upper (D 8) (R 8) [6,96,288,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1548 : Route 9 := (fun mask => (mask,id))

def c1548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1548 : Upper (D 8) (R 8) [6,96,288,17,160,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,160,1] 13 (by decide) (choices 1) [8,128] r1548 c1548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u208
  · exact u209

def b1549 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 98 292 25 176 40 193 193 449), lower := (rows 7 98 292 25 176 40 64 128 256), losses := [] }

theorem u1549 : Upper (D 8) (R 8) [6,96,288,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1549 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1550 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 292 25 176 96 201 137 393), lower := (rows 7 98 292 25 176 96 64 128 256), losses := [] }

theorem u1550 : Upper (D 8) (R 8) [6,96,288,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1551 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 292 25 176 160 73 201 329), lower := (rows 7 98 292 25 176 160 64 128 256), losses := [] }

theorem u1551 : Upper (D 8) (R 8) [6,96,288,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1552 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 292 56 145 33 200 200 456), lower := (rows 7 98 292 56 145 33 64 128 256), losses := [] }

theorem u1552 : Upper (D 8) (R 8) [6,96,288,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1553 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 98 292 56 145 40 193 193 449), lower := (rows 7 98 292 56 145 40 64 128 256), losses := [] }

theorem u1553 : Upper (D 8) (R 8) [6,96,288,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1553 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1554 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 292 56 145 96 201 137 393), lower := (rows 7 98 292 56 145 96 64 128 256), losses := [] }

theorem u1554 : Upper (D 8) (R 8) [6,96,288,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1555 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 292 56 145 160 73 201 329), lower := (rows 7 98 292 56 145 160 64 128 256), losses := [] }

theorem u1555 : Upper (D 8) (R 8) [6,96,288,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1556 : PairBound 9 := { available := 193, camps := [], pairs := [(4,5)], upper := (rows 7 98 292 56 152 33 193 193 449), lower := (rows 7 98 292 56 152 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 24 0 97 161 289), good := (rows 455 450 452 472 152 449 64 128 256) }] }

theorem u1556 : Upper (D 8) (R 8) [6,96,288,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1556 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1557 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 292 56 152 96 193 129 385), lower := (rows 7 98 292 56 152 96 64 128 256), losses := [] }

theorem u1557 : Upper (D 8) (R 8) [6,96,288,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1558 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 292 56 152 160 65 193 321), lower := (rows 7 98 292 56 152 160 64 128 256), losses := [] }

theorem u1558 : Upper (D 8) (R 8) [6,96,288,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1559 : Route 9 := (fun mask => (mask,id))

def c1559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1559 : Upper (D 8) (R 8) [6,96,288,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,48,192,1] 13 (by decide) (choices 1) [1,8,128] r1559 c1559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u210
  · exact u211
  · exact u212

#print axioms u1559
end Delivery.IrregularNine14.P08
