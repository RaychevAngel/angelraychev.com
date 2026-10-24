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

def b1500 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 7 42 21 200 112 288 65 130 386), lower := (rows 7 42 21 200 112 288 65 128 256), losses := [] }

theorem u1500 : Upper (D 7) (R 7) [6,40,17,192,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1500 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1501 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 7 42 21 200 112 288 66 129 385), lower := (rows 7 42 21 200 112 288 66 128 256), losses := [] }

theorem u1501 : Upper (D 7) (R 7) [6,40,17,192,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1501 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1502 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 21 200 112 288 192 131 259), lower := (rows 7 42 21 200 112 288 192 128 256), losses := [] }

theorem u1502 : Upper (D 7) (R 7) [6,40,17,192,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1502 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1503 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 42 21 200 336 33 66 160 416), lower := (rows 7 42 21 200 336 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 72 80 37 64 167 295), good := (rows 421 424 437 216 344 417 472 128 256) }] }

theorem u1503 : Upper (D 7) (R 7) [6,40,17,192,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1504 : Route 9 := (fun mask => (mask,id))

def c1504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1504 : Upper (D 7) (R 7) [6,40,17,192,320,1,32] 13 := by
  apply FastRouting.sound _ _ [6,40,17,192,320,1,32] 13 (by decide) (choices 1) [2] r1504 c1504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u52

def b1505 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 21 200 336 33 192 162 290), lower := (rows 7 42 21 200 336 33 192 128 256), losses := [] }

theorem u1505 : Upper (D 7) (R 7) [6,40,17,192,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1506 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 7 42 21 200 336 34 65 160 416), lower := (rows 7 42 21 200 336 34 65 128 256), losses := [] }

theorem u1506 : Upper (D 7) (R 7) [6,40,17,192,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1507 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 3, region := 34, targets := 64 },{ cop := 7, region := 106, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 21 200 336 34 96 129 385), lower := (rows 7 42 21 200 336 34 96 128 256), losses := [] }

theorem u1507 : Upper (D 7) (R 7) [6,40,17,192,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1508 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 21 200 336 34 192 161 289), lower := (rows 7 42 21 200 336 34 192 128 256), losses := [] }

theorem u1508 : Upper (D 7) (R 7) [6,40,17,192,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1509 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 21 265 112 160 66 192 448), lower := (rows 7 42 21 265 112 160 66 128 256), losses := [] }

theorem u1509 : Upper (D 7) (R 7) [6,40,17,257,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1510 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 265 112 160 192 194 322), lower := (rows 7 42 21 265 112 160 192 128 256), losses := [] }

theorem u1510 : Upper (D 7) (R 7) [6,40,17,257,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1511 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 98, targets := 128 },{ cop := 5, region := 144, targets := 2 }], pairs := [(1,0),(1,7),(4,0),(4,1)], upper := (rows 7 42 21 265 208 96 66 160 416), lower := (rows 7 42 21 265 208 96 66 128 256), losses := [] }

theorem u1511 : Upper (D 7) (R 7) [6,40,17,257,192,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1512 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 392, targets := 96 },{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(4,0)], upper := (rows 7 42 21 265 208 96 96 130 386), lower := (rows 7 42 21 265 208 96 96 128 256), losses := [] }

theorem u1512 : Upper (D 7) (R 7) [6,40,17,257,192,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1513 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 265 208 96 192 162 290), lower := (rows 7 42 21 265 208 96 192 128 256), losses := [] }

theorem u1513 : Upper (D 7) (R 7) [6,40,17,257,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1514 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 6, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 21 266 112 160 65 192 448), lower := (rows 7 42 21 266 112 160 65 128 256), losses := [] }

theorem u1514 : Upper (D 7) (R 7) [6,40,17,258,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1515 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 266 112 160 192 193 321), lower := (rows 7 42 21 266 112 160 192 128 256), losses := [] }

theorem u1515 : Upper (D 7) (R 7) [6,40,17,258,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1516 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 1 },{ cop := 0, region := 244, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 42 21 266 208 96 65 160 416), lower := (rows 7 42 21 266 208 96 65 128 256), losses := [] }

theorem u1516 : Upper (D 7) (R 7) [6,40,17,258,192,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1517 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 21 266 208 96 96 129 385), lower := (rows 7 42 21 266 208 96 96 128 256), losses := [] }

theorem u1517 : Upper (D 7) (R 7) [6,40,17,258,192,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1518 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 266 208 96 192 161 289), lower := (rows 7 42 21 266 208 96 192 128 256), losses := [] }

theorem u1518 : Upper (D 7) (R 7) [6,40,17,258,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1519 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 6, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 21 328 112 160 65 130 386), lower := (rows 7 42 21 328 112 160 65 128 256), losses := [] }

theorem u1519 : Upper (D 7) (R 7) [6,40,17,320,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1520 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 21 328 112 160 66 129 385), lower := (rows 7 42 21 328 112 160 66 128 256), losses := [] }

theorem u1520 : Upper (D 7) (R 7) [6,40,17,320,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1521 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 328 112 160 192 131 259), lower := (rows 7 42 21 328 112 160 192 128 256), losses := [] }

theorem u1521 : Upper (D 7) (R 7) [6,40,17,320,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1522 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 42 21 328 208 33 66 160 416), lower := (rows 7 42 21 328 208 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 72 80 37 64 167 295), good := (rows 421 424 437 344 216 417 472 128 256) }] }

theorem u1522 : Upper (D 7) (R 7) [6,40,17,320,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1523 : Route 9 := (fun mask => (mask,id))

def c1523 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1523 : Upper (D 7) (R 7) [6,40,17,320,192,1,32] 13 := by
  apply FastRouting.sound _ _ [6,40,17,320,192,1,32] 13 (by decide) (choices 1) [2] r1523 c1523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u53

def b1524 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 328 208 33 192 162 290), lower := (rows 7 42 21 328 208 33 192 128 256), losses := [] }

theorem u1524 : Upper (D 7) (R 7) [6,40,17,320,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1525 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 7 42 21 328 208 34 65 160 416), lower := (rows 7 42 21 328 208 34 65 128 256), losses := [] }

theorem u1525 : Upper (D 7) (R 7) [6,40,17,320,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1526 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 21 328 208 34 96 129 385), lower := (rows 7 42 21 328 208 34 96 128 256), losses := [] }

theorem u1526 : Upper (D 7) (R 7) [6,40,17,320,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1527 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 21 328 208 34 192 161 289), lower := (rows 7 42 21 328 208 34 192 128 256), losses := [] }

theorem u1527 : Upper (D 7) (R 7) [6,40,17,320,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1528 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 7 42 21 328 208 160 65 162 290), lower := (rows 7 42 21 328 208 160 65 128 256), losses := [] }

theorem u1528 : Upper (D 7) (R 7) [6,40,17,320,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1529 : Route 9 := (fun mask => (mask,id))

def c1529 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1529 : Upper (D 7) (R 7) [6,40,17,320,192,128,2] 13 := by
  apply FastRouting.sound _ _ [6,40,17,320,192,128,2] 13 (by decide) (choices 1) [1,32] r1529 c1529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u54
  · exact u55

def r1530 : Route 9 := (fun mask => (mask,id))

def c1530 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1530 : Upper (D 7) (R 7) [6,40,17,320,192,128,32] 13 := by
  apply FastRouting.sound _ _ [6,40,17,320,192,128,32] 13 (by decide) (choices 1) [1,2] r1530 c1530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u56
  · exact u57

def b1531 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 3, region := 162, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(3,7)], upper := (rows 7 42 52 73 336 160 65 130 386), lower := (rows 7 42 52 73 336 160 65 128 256), losses := [] }

theorem u1531 : Upper (D 7) (R 7) [6,40,48,65,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1532 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 0, region := 72, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(3,7)], upper := (rows 7 42 52 73 336 160 66 129 385), lower := (rows 7 42 52 73 336 160 66 128 256), losses := [] }

theorem u1532 : Upper (D 7) (R 7) [6,40,48,65,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1533 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(3,5),(4,5)], upper := (rows 7 42 52 73 336 160 192 131 259), lower := (rows 7 42 52 73 336 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 224 224 128 256), good := (rows 6 106 116 106 372 224 224 224 256) }] }

theorem u1533 : Upper (D 7) (R 7) [6,40,48,65,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1534 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 52 200 336 33 65 130 386), lower := (rows 7 42 52 200 336 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 80 32 64 131 259), good := (rows 390 426 52 216 344 416 472 128 256) }] }

theorem u1534 : Upper (D 7) (R 7) [6,40,48,192,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1535 : Route 9 := (fun mask => (mask,id))

def c1535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1535 : Upper (D 7) (R 7) [6,40,48,192,320,1,2] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,320,1,2] 13 (by decide) (choices 1) [1] r1535 c1535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u58

def b1536 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 52 200 336 33 192 131 259), lower := (rows 7 42 52 200 336 33 192 128 256), losses := [] }

theorem u1536 : Upper (D 7) (R 7) [6,40,48,192,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1537 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 4, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 52 328 81 160 65 130 386), lower := (rows 7 42 52 328 81 160 65 128 256), losses := [] }

theorem u1537 : Upper (D 7) (R 7) [6,40,48,320,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1538 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 52 328 81 160 66 129 385), lower := (rows 7 42 52 328 81 160 66 128 256), losses := [] }

theorem u1538 : Upper (D 7) (R 7) [6,40,48,320,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1539 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(1,0),(2,0),(3,5),(4,5)], upper := (rows 7 42 52 328 81 160 192 131 259), lower := (rows 7 42 52 328 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 224 224 128 256), good := (rows 6 106 116 362 116 224 224 224 256) }] }

theorem u1539 : Upper (D 7) (R 7) [6,40,48,320,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1540 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 52 328 208 33 65 130 386), lower := (rows 7 42 52 328 208 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 80 32 64 131 259), good := (rows 390 426 52 344 216 416 472 128 256) }] }

theorem u1540 : Upper (D 7) (R 7) [6,40,48,320,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1541 : Route 9 := (fun mask => (mask,id))

def c1541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1541 : Upper (D 7) (R 7) [6,40,48,320,192,1,2] 13 := by
  apply FastRouting.sound _ _ [6,40,48,320,192,1,2] 13 (by decide) (choices 1) [1] r1541 c1541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u59

def b1542 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 52 328 208 33 192 131 259), lower := (rows 7 42 52 328 208 33 192 128 256), losses := [] }

theorem u1542 : Upper (D 7) (R 7) [6,40,48,320,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1543 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 7 42 69 25 274 160 96 192 448), lower := (rows 7 42 69 25 274 160 96 128 256), losses := [] }

theorem u1543 : Upper (D 7) (R 7) [6,40,65,17,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1544 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,5),(1,0),(2,1),(4,0)], upper := (rows 7 42 69 25 274 160 192 224 352), lower := (rows 7 42 69 25 274 160 192 128 256), losses := [{ target := 5, region := (rows 19 2 6 24 16 0 224 128 256), good := (rows 7 79 69 25 287 192 192 192 256) }] }

theorem u1544 : Upper (D 7) (R 7) [6,40,65,17,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1545 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 25 336 160 66 160 416), lower := (rows 7 42 69 25 336 160 66 128 256), losses := [] }

theorem u1545 : Upper (D 7) (R 7) [6,40,65,17,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1546 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 7 42 69 25 336 160 96 130 386), lower := (rows 7 42 69 25 336 160 96 128 256), losses := [] }

theorem u1546 : Upper (D 7) (R 7) [6,40,65,17,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1547 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 162, targets := 64 }], pairs := [(0,5),(1,0),(1,6),(4,0)], upper := (rows 7 42 69 25 336 160 192 162 290), lower := (rows 7 42 69 25 336 160 192 128 256), losses := [{ target := 5, region := (rows 3 2 6 8 16 0 224 128 256), good := (rows 7 79 69 25 336 192 192 192 256) }] }

theorem u1547 : Upper (D 7) (R 7) [6,40,65,17,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1548 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 26 208 288 65 160 416), lower := (rows 7 42 69 26 208 288 65 128 256), losses := [] }

theorem u1548 : Upper (D 7) (R 7) [6,40,65,18,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1548 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1549 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,1),(4,1)], upper := (rows 7 42 69 26 208 288 96 129 385), lower := (rows 7 42 69 26 208 288 96 128 256), losses := [] }

theorem u1549 : Upper (D 7) (R 7) [6,40,65,18,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1549 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1550 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 69 26 208 288 192 161 289), lower := (rows 7 42 69 26 208 288 192 128 256), losses := [] }

theorem u1550 : Upper (D 7) (R 7) [6,40,65,18,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1550 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1551 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 26 336 160 65 160 416), lower := (rows 7 42 69 26 336 160 65 128 256), losses := [] }

theorem u1551 : Upper (D 7) (R 7) [6,40,65,18,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1552 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,1),(2,7),(4,1)], upper := (rows 7 42 69 26 336 160 96 129 385), lower := (rows 7 42 69 26 336 160 96 128 256), losses := [] }

theorem u1552 : Upper (D 7) (R 7) [6,40,65,18,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1553 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 69 26 336 160 192 161 289), lower := (rows 7 42 69 26 336 160 192 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 224 224 128 256), good := (rows 6 106 100 26 378 224 224 224 256) }] }

theorem u1553 : Upper (D 7) (R 7) [6,40,65,18,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1554 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 26 400 96 65 160 416), lower := (rows 7 42 69 26 400 96 65 128 256), losses := [] }

theorem u1554 : Upper (D 7) (R 7) [6,40,65,18,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1555 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 69 26 400 96 96 129 385), lower := (rows 7 42 69 26 400 96 96 128 256), losses := [] }

theorem u1555 : Upper (D 7) (R 7) [6,40,65,18,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1556 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 69 26 400 96 192 161 289), lower := (rows 7 42 69 26 400 96 192 128 256), losses := [] }

theorem u1556 : Upper (D 7) (R 7) [6,40,65,18,384,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1557 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 88 146 288 65 160 416), lower := (rows 7 42 69 88 146 288 65 128 256), losses := [] }

theorem u1557 : Upper (D 7) (R 7) [6,40,65,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1557 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1558 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,7),(2,1),(2,7)], upper := (rows 7 42 69 88 146 288 96 129 385), lower := (rows 7 42 69 88 146 288 96 128 256), losses := [] }

theorem u1558 : Upper (D 7) (R 7) [6,40,65,80,130,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1558 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1559 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 69 88 146 288 192 161 289), lower := (rows 7 42 69 88 146 288 192 128 256), losses := [] }

theorem u1559 : Upper (D 7) (R 7) [6,40,65,80,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1559 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1559
end Delivery.IrregularNine14.P07
