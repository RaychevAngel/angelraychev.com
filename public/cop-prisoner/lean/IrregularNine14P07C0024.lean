import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0000

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1440 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 178, targets := 64 },{ cop := 1, region := 72, targets := 2 },{ cop := 1, region := 72, targets := 128 }], pairs := [(1,6),(3,1),(3,7),(4,6)], upper := (rows 7 35 324 73 146 160 96 152 280), lower := (rows 7 35 324 73 146 160 96 128 256), losses := [] }

theorem u1440 : Upper (D 7) (R 7) [6,33,320,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1441 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 324 73 152 160 66 176 304), lower := (rows 7 35 324 73 152 160 66 128 256), losses := [] }

theorem u1441 : Upper (D 7) (R 7) [6,33,320,65,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1442 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 3, region := 178, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 324 73 152 160 80 162 290), lower := (rows 7 35 324 73 152 160 80 128 256), losses := [] }

theorem u1442 : Upper (D 7) (R 7) [6,33,320,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1442 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1443 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 178, targets := 64 },{ cop := 1, region := 72, targets := 2 },{ cop := 1, region := 72, targets := 128 }], pairs := [(1,6),(3,1),(3,7),(4,6)], upper := (rows 7 35 324 73 152 160 96 146 274), lower := (rows 7 35 324 73 152 160 96 128 256), losses := [] }

theorem u1443 : Upper (D 7) (R 7) [6,33,320,65,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1444 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 72, targets := 161 }], pairs := [(3,0),(3,5),(3,7)], upper := (rows 7 35 324 74 145 160 72 176 304), lower := (rows 7 35 324 74 145 160 72 128 256), losses := [] }

theorem u1444 : Upper (D 7) (R 7) [6,33,320,66,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1444 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1445 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 420, targets := 3 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 7 35 324 74 145 160 80 168 296), lower := (rows 7 35 324 74 145 160 80 128 256), losses := [] }

theorem u1445 : Upper (D 7) (R 7) [6,33,320,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1445 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1446 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 405, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 324 74 145 160 96 152 280), lower := (rows 7 35 324 74 145 160 96 128 256), losses := [] }

theorem u1446 : Upper (D 7) (R 7) [6,33,320,66,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1447 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 324 74 152 160 65 176 304), lower := (rows 7 35 324 74 152 160 65 128 256), losses := [] }

theorem u1447 : Upper (D 7) (R 7) [6,33,320,66,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1448 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 7 35 324 74 152 160 80 161 289), lower := (rows 7 35 324 74 152 160 80 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 187 88 131 259), good := (rows 421 417 324 508 252 160 112 160 256) }] }

theorem u1448 : Upper (D 7) (R 7) [6,33,320,66,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1448 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1449 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 405, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 324 74 152 160 96 145 273), lower := (rows 7 35 324 74 152 160 96 128 256), losses := [] }

theorem u1449 : Upper (D 7) (R 7) [6,33,320,66,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1450 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 420, targets := 3 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7),(2,0),(2,1)], upper := (rows 7 35 324 88 145 40 66 160 416), lower := (rows 7 35 324 88 145 40 66 128 256), losses := [] }

theorem u1450 : Upper (D 7) (R 7) [6,33,320,80,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1450 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1451 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 144, targets := 96 },{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0),(4,5),(4,6)], upper := (rows 7 35 324 88 145 40 96 130 386), lower := (rows 7 35 324 88 145 40 96 128 256), losses := [] }

theorem u1451 : Upper (D 7) (R 7) [6,33,320,80,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1451 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1452 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 324 88 145 40 192 162 290), lower := (rows 7 35 324 88 145 40 192 128 256), losses := [] }

theorem u1452 : Upper (D 7) (R 7) [6,33,320,80,129,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1452 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1453 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 420, targets := 3 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(3,0)], upper := (rows 7 35 324 88 145 160 66 168 296), lower := (rows 7 35 324 88 145 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 184 67 152 280), good := (rows 70 98 324 508 508 160 66 160 256) }] }

theorem u1453 : Upper (D 7) (R 7) [6,33,320,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1454 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 179, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 324 88 145 160 72 162 290), lower := (rows 7 35 324 88 145 160 72 128 256), losses := [] }

theorem u1454 : Upper (D 7) (R 7) [6,33,320,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1454 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1455 : Route 9 := (fun mask => (mask,id))

def c1455 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1455 : Upper (D 7) (R 7) [6,33,320,80,129,128,32] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80,129,128,32] 13 (by decide) (choices 1) [2,8] r1455 c1455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u48
  · exact u49

def b1456 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 420, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 35 324 88 146 160 65 168 296), lower := (rows 7 35 324 88 146 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 76 72 17 253 64 204 332), good := (rows 438 50 492 508 178 160 508 160 256) }] }

theorem u1456 : Upper (D 7) (R 7) [6,33,320,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1457 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 179, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 324 88 146 160 72 161 289), lower := (rows 7 35 324 88 146 160 72 128 256), losses := [] }

theorem u1457 : Upper (D 7) (R 7) [6,33,320,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1457 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1458 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(0,7),(2,7),(3,0),(3,1)], upper := (rows 7 35 324 88 146 160 96 137 265), lower := (rows 7 35 324 88 146 160 96 128 256), losses := [{ target := 7, region := (rows 17 2 28 24 16 32 98 0 280), good := (rows 71 99 324 349 351 96 96 0 256) }] }

theorem u1458 : Upper (D 7) (R 7) [6,33,320,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1459 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 72, targets := 129 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(3,7)], upper := (rows 7 35 324 104 145 160 66 152 280), lower := (rows 7 35 324 104 145 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 26 16 176 67 144 272), good := (rows 78 106 324 104 508 160 74 160 256) }] }

theorem u1459 : Upper (D 7) (R 7) [6,33,320,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1460 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 179, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 324 104 145 160 72 146 274), lower := (rows 7 35 324 104 145 160 72 128 256), losses := [] }

theorem u1460 : Upper (D 7) (R 7) [6,33,320,96,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1460 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1461 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 324 104 145 160 80 138 266), lower := (rows 7 35 324 104 145 160 80 128 256), losses := [] }

theorem u1461 : Upper (D 7) (R 7) [6,33,320,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1461 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1462 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 388, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 35 324 104 146 48 65 136 392), lower := (rows 7 35 324 104 146 48 65 128 256), losses := [] }

theorem u1462 : Upper (D 7) (R 7) [6,33,320,96,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1462 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1463 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 179, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 324 104 146 48 72 129 385), lower := (rows 7 35 324 104 146 48 72 128 256), losses := [] }

theorem u1463 : Upper (D 7) (R 7) [6,33,320,96,130,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1463 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1464 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 324 104 146 48 192 137 265), lower := (rows 7 35 324 104 146 48 192 128 256), losses := [] }

theorem u1464 : Upper (D 7) (R 7) [6,33,320,96,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1464 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1465 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 72, targets := 2 },{ cop := 1, region := 72, targets := 128 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 35 324 104 146 160 65 152 280), lower := (rows 7 35 324 104 146 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 76 76 19 255 64 193 321), good := (rows 446 434 492 492 178 160 508 160 256) }] }

theorem u1465 : Upper (D 7) (R 7) [6,33,320,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1466 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 179, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 324 104 146 160 72 145 273), lower := (rows 7 35 324 104 146 160 72 128 256), losses := [] }

theorem u1466 : Upper (D 7) (R 7) [6,33,320,96,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1466 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1467 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 324 104 146 160 80 137 265), lower := (rows 7 35 324 104 146 160 80 128 256), losses := [] }

theorem u1467 : Upper (D 7) (R 7) [6,33,320,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1467 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1468 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 1, region := 72, targets := 2 }], pairs := [(0,5),(2,5),(3,1)], upper := (rows 7 35 324 104 152 48 65 130 386), lower := (rows 7 35 324 104 152 48 65 128 256), losses := [] }

theorem u1468 : Upper (D 7) (R 7) [6,33,320,96,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1468 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1469 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 72, targets := 129 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(3,0),(3,7)], upper := (rows 7 35 324 104 152 48 66 129 385), lower := (rows 7 35 324 104 152 48 66 128 256), losses := [] }

theorem u1469 : Upper (D 7) (R 7) [6,33,320,96,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1469 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1470 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 324 104 152 48 192 131 259), lower := (rows 7 35 324 104 152 48 192 128 256), losses := [] }

theorem u1470 : Upper (D 7) (R 7) [6,33,320,96,136,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1470 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1471 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 72, targets := 2 },{ cop := 1, region := 72, targets := 128 }], pairs := [(2,0),(3,0),(3,1),(3,7)], upper := (rows 7 35 324 104 152 160 65 146 274), lower := (rows 7 35 324 104 152 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 76 81 243 64 131 259), good := (rows 446 434 380 124 184 160 508 160 256) }] }

theorem u1471 : Upper (D 7) (R 7) [6,33,320,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1472 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 72, targets := 129 }], pairs := [(2,1),(3,0),(3,1),(3,7)], upper := (rows 7 35 324 104 152 160 66 145 273), lower := (rows 7 35 324 104 152 160 66 128 256), losses := [{ target := 1, region := (rows 1 0 68 76 81 243 64 131 259), good := (rows 445 433 380 124 184 160 508 160 256) }] }

theorem u1472 : Upper (D 7) (R 7) [6,33,320,96,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1473 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 324 104 152 160 80 131 259), lower := (rows 7 35 324 104 152 160 80 128 256), losses := [] }

theorem u1473 : Upper (D 7) (R 7) [6,33,320,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1473 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1474 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 136, targets := 2 },{ cop := 1, region := 136, targets := 64 }], pairs := [(2,0),(3,1),(3,6)], upper := (rows 7 35 324 137 208 48 66 168 296), lower := (rows 7 35 324 137 208 48 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 56 67 136 264), good := (rows 70 98 324 508 240 48 66 128 256) }] }

theorem u1474 : Upper (D 7) (R 7) [6,33,320,129,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1474 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1475 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 324 137 208 48 72 162 290), lower := (rows 7 35 324 137 208 48 72 128 256), losses := [] }

theorem u1475 : Upper (D 7) (R 7) [6,33,320,129,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1475 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1476 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 136, targets := 96 },{ cop := 3, region := 112, targets := 1 }], pairs := [(3,5),(3,6),(4,0)], upper := (rows 7 35 324 137 208 48 96 138 266), lower := (rows 7 35 324 137 208 48 96 128 256), losses := [] }

theorem u1476 : Upper (D 7) (R 7) [6,33,320,129,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1476 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1477 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 468, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 35 324 138 208 40 65 176 304), lower := (rows 7 35 324 138 208 40 65 128 256), losses := [{ target := 0, region := (rows 0 2 84 11 84 107 64 213 341), good := (rows 446 426 500 170 500 40 508 128 256) }] }

theorem u1477 : Upper (D 7) (R 7) [6,33,320,130,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1477 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1478 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 324 138 208 40 80 161 289), lower := (rows 7 35 324 138 208 40 80 128 256), losses := [] }

theorem u1478 : Upper (D 7) (R 7) [6,33,320,130,192,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1478 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1479 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 468, targets := 2 },{ cop := 3, region := 112, targets := 1 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 7 35 324 138 208 40 96 145 273), lower := (rows 7 35 324 138 208 40 96 128 256), losses := [] }

theorem u1479 : Upper (D 7) (R 7) [6,33,320,130,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1479 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1480 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 136, targets := 65 }], pairs := [(2,0),(3,0),(3,6)], upper := (rows 7 35 324 138 208 48 65 168 296), lower := (rows 7 35 324 138 208 48 65 128 256), losses := [{ target := 0, region := (rows 0 2 84 11 84 117 64 195 323), good := (rows 446 426 500 394 500 52 508 128 256) }] }

theorem u1480 : Upper (D 7) (R 7) [6,33,320,130,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1480 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1481 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 324 138 208 48 72 161 289), lower := (rows 7 35 324 138 208 48 72 128 256), losses := [] }

theorem u1481 : Upper (D 7) (R 7) [6,33,320,130,192,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1481 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1482 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 96 },{ cop := 3, region := 112, targets := 1 }], pairs := [(3,5),(3,6),(4,0)], upper := (rows 7 35 324 138 208 48 96 137 265), lower := (rows 7 35 324 138 208 48 96 128 256), losses := [] }

theorem u1482 : Upper (D 7) (R 7) [6,33,320,130,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1482 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1483 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 73 304 160 66 192 448), lower := (rows 7 42 21 73 304 160 66 128 256), losses := [] }

theorem u1483 : Upper (D 7) (R 7) [6,40,17,65,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1484 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,0),(1,6),(3,5),(4,0)], upper := (rows 7 42 21 73 304 160 192 194 322), lower := (rows 7 42 21 73 304 160 192 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 16 224 0 128 256), good := (rows 7 42 21 43 304 160 160 160 256) }] }

theorem u1484 : Upper (D 7) (R 7) [6,40,17,65,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1485 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7),(4,0)], upper := (rows 7 42 21 73 336 160 66 160 416), lower := (rows 7 42 21 73 336 160 66 128 256), losses := [] }

theorem u1485 : Upper (D 7) (R 7) [6,40,17,65,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1486 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(3,1),(4,0)], upper := (rows 7 42 21 73 336 160 96 130 386), lower := (rows 7 42 21 73 336 160 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 160 226 128 256), good := (rows 77 104 29 73 336 224 96 224 256) }] }

theorem u1486 : Upper (D 7) (R 7) [6,40,17,65,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1487 : Route 9 := (fun mask => (mask,id))

def c1487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1487 : Upper (D 7) (R 7) [6,40,17,65,320,128,128] 13 := by
  apply FastRouting.sound _ _ [6,40,17,65,320,128,128] 13 (by decide) (choices 1) [2,32] r1487 c1487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u50
  · exact u51

def b1488 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7),(4,0)], upper := (rows 7 42 21 73 400 160 66 224 352), lower := (rows 7 42 21 73 400 160 66 128 256), losses := [] }

theorem u1488 : Upper (D 7) (R 7) [6,40,17,65,384,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1489 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,7),(4,0)], upper := (rows 7 42 21 73 400 160 96 194 322), lower := (rows 7 42 21 73 400 160 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 13 16 176 246 128 256), good := (rows 77 104 125 73 496 224 96 224 256) },{ target := 7, region := (rows 1 2 4 9 16 32 98 0 259), good := (rows 335 362 285 329 272 96 96 0 256) }] }

theorem u1489 : Upper (D 7) (R 7) [6,40,17,65,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1490 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 42 21 74 208 288 65 160 416), lower := (rows 7 42 21 74 208 288 65 128 256), losses := [] }

theorem u1490 : Upper (D 7) (R 7) [6,40,17,66,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1490 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1491 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 42 21 74 208 288 96 129 385), lower := (rows 7 42 21 74 208 288 96 128 256), losses := [] }

theorem u1491 : Upper (D 7) (R 7) [6,40,17,66,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1491 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1492 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 21 74 208 288 192 161 289), lower := (rows 7 42 21 74 208 288 192 128 256), losses := [] }

theorem u1492 : Upper (D 7) (R 7) [6,40,17,66,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1492 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1493 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 74 304 160 65 192 448), lower := (rows 7 42 21 74 304 160 65 128 256), losses := [] }

theorem u1493 : Upper (D 7) (R 7) [6,40,17,66,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1494 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 5, region := 74, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 21 74 304 160 192 193 321), lower := (rows 7 42 21 74 304 160 192 128 256), losses := [] }

theorem u1494 : Upper (D 7) (R 7) [6,40,17,66,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1495 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 21 74 336 160 65 160 416), lower := (rows 7 42 21 74 336 160 65 128 256), losses := [] }

theorem u1495 : Upper (D 7) (R 7) [6,40,17,66,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1496 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 21 74 336 160 96 129 385), lower := (rows 7 42 21 74 336 160 96 128 256), losses := [] }

theorem u1496 : Upper (D 7) (R 7) [6,40,17,66,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1497 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 5, region := 74, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 21 74 336 160 192 161 289), lower := (rows 7 42 21 74 336 160 192 128 256), losses := [] }

theorem u1497 : Upper (D 7) (R 7) [6,40,17,66,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1498 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 21 74 400 160 65 224 352), lower := (rows 7 42 21 74 400 160 65 128 256), losses := [] }

theorem u1498 : Upper (D 7) (R 7) [6,40,17,66,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1499 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 21 74 400 160 96 193 321), lower := (rows 7 42 21 74 400 160 96 128 256), losses := [] }

theorem u1499 : Upper (D 7) (R 7) [6,40,17,66,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1499
end Delivery.IrregularNine14.P07
