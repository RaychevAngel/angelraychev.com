import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0001

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1440 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 80, targets := 129 }], pairs := [(1,0),(2,5),(3,5),(4,0),(4,7)], upper := (rows 35 70 133 152 336 288 96 137 265), lower := (rows 35 70 133 152 336 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 304 304 377 128 256), good := (rows 114 70 198 248 368 368 112 128 368) },{ target := 5, region := (rows 1 2 5 11 18 0 64 133 261), good := (rows 415 478 397 152 336 256 64 128 256) }] }

theorem u1440 : Upper (D 9) (R 9) [34,68,129,144,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1440 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1441 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 71, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 70 133 168 273 48 72 448 320), lower := (rows 35 70 133 168 273 48 72 128 256), losses := [] }

theorem u1441 : Upper (D 9) (R 9) [34,68,129,160,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1441 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1442 : Route 9 := (fun mask => (mask,id))

def c1442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1442 : Upper (D 9) (R 9) [34,68,129,160,257,16,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,257,16,256] 13 (by decide) (choices 1) [8,64] r1442 c1442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u64
  · exact u65

def b1443 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 1, region := 305, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 35 70 133 168 273 288 72 208 336), lower := (rows 35 70 133 168 273 288 72 128 256), losses := [] }

theorem u1443 : Upper (D 9) (R 9) [34,68,129,160,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1443 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1444 : Route 9 := (fun mask => (mask,id))

def c1444 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1444 : Upper (D 9) (R 9) [34,68,129,160,257,256,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,257,256,16] 13 (by decide) (choices 1) [8,64] r1444 c1444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u66
  · exact u67

def b1445 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 0, region := 454, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8)], upper := (rows 35 70 133 168 280 48 65 448 320), lower := (rows 35 70 133 168 280 48 65 128 256), losses := [] }

theorem u1445 : Upper (D 9) (R 9) [34,68,129,160,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1445 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1446 : Route 9 := (fun mask => (mask,id))

def c1446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1446 : Upper (D 9) (R 9) [34,68,129,160,264,16,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,264,16,256] 13 (by decide) (choices 1) [1,64] r1446 c1446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u68
  · exact u69

def b1447 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0),(4,0)], upper := (rows 35 70 133 168 280 288 65 208 336), lower := (rows 35 70 133 168 280 288 65 128 256), losses := [] }

theorem u1447 : Upper (D 9) (R 9) [34,68,129,160,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1447 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1448 : Route 9 := (fun mask => (mask,id))

def c1448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1448 : Upper (D 9) (R 9) [34,68,129,160,264,256,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,264,256,16] 13 (by decide) (choices 1) [1,64] r1448 c1448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u70
  · exact u71

def b1449 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 0, region := 396, targets := 64 }], pairs := [(1,5),(1,7),(1,8),(2,6)], upper := (rows 35 70 133 168 336 48 65 392 264), lower := (rows 35 70 133 168 336 48 65 128 256), losses := [] }

theorem u1449 : Upper (D 9) (R 9) [34,68,129,160,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1449 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1450 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 71, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 70 133 168 336 48 72 385 257), lower := (rows 35 70 133 168 336 48 72 128 256), losses := [] }

theorem u1450 : Upper (D 9) (R 9) [34,68,129,160,320,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1450 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1451 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 133 168 336 48 320 137 265), lower := (rows 35 70 133 168 336 48 320 128 256), losses := [] }

theorem u1451 : Upper (D 9) (R 9) [34,68,129,160,320,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1451 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1452 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0),(4,0)], upper := (rows 35 70 133 168 336 288 65 152 280), lower := (rows 35 70 133 168 336 288 65 128 256), losses := [] }

theorem u1452 : Upper (D 9) (R 9) [34,68,129,160,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1452 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1453 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 1, region := 305, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 35 70 133 168 336 288 72 145 273), lower := (rows 35 70 133 168 336 288 72 128 256), losses := [] }

theorem u1453 : Upper (D 9) (R 9) [34,68,129,160,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1453 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1454 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 0, region := 140, targets := 256 }], pairs := [(0,6),(2,6),(2,8),(3,6)], upper := (rows 35 70 133 168 336 288 80 137 265), lower := (rows 35 70 133 168 336 288 80 128 256), losses := [] }

theorem u1454 : Upper (D 9) (R 9) [34,68,129,160,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1454 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1455 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 74, targets := 289 }], pairs := [(1,0),(1,5),(1,8)], upper := (rows 35 70 133 200 273 48 72 416 288), lower := (rows 35 70 133 200 273 48 72 128 256), losses := [] }

theorem u1455 : Upper (D 9) (R 9) [34,68,129,192,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1455 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1456 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 392, targets := 33 }], pairs := [(1,0),(2,5),(3,0),(3,5)], upper := (rows 35 70 133 200 273 48 96 392 264), lower := (rows 35 70 133 200 273 48 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 127 16 48 113 255 383), good := (rows 490 462 462 456 504 504 488 128 256) },{ target := 5, region := (rows 1 2 21 74 21 0 64 203 331), good := (rows 415 478 405 456 405 20 456 128 256) }] }

theorem u1456 : Upper (D 9) (R 9) [34,68,129,192,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1456 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1457 : Route 9 := (fun mask => (mask,id))

def c1457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1457 : Upper (D 9) (R 9) [34,68,129,192,257,16,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,257,16,256] 13 (by decide) (choices 1) [8,32] r1457 c1457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u72
  · exact u73

def b1458 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 74, targets := 289 }], pairs := [(1,0),(1,5),(1,8),(3,0)], upper := (rows 35 70 133 200 273 288 72 176 304), lower := (rows 35 70 133 200 273 288 72 128 256), losses := [] }

theorem u1458 : Upper (D 9) (R 9) [34,68,129,192,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1458 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1459 : Route 9 := (fun mask => (mask,id))

def c1459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1459 : Upper (D 9) (R 9) [34,68,129,192,257,256,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,257,256,16] 13 (by decide) (choices 1) [8,32] r1459 c1459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u74
  · exact u75

def b1460 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(1,0),(2,5),(3,0),(3,5),(4,5)], upper := (rows 35 70 133 200 273 288 96 152 280), lower := (rows 35 70 133 200 273 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 28 16 304 369 144 272), good := (rows 98 78 206 200 504 352 96 128 352) },{ target := 5, region := (rows 1 2 21 10 21 0 64 131 259), good := (rows 415 478 405 200 405 256 64 128 256) }] }

theorem u1460 : Upper (D 9) (R 9) [34,68,129,192,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1460 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1461 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 74, targets := 288 }], pairs := [(1,5),(1,8),(3,5),(3,8)], upper := (rows 35 70 133 200 280 48 65 416 288), lower := (rows 35 70 133 200 280 48 65 128 256), losses := [] }

theorem u1461 : Upper (D 9) (R 9) [34,68,129,192,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1461 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1462 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 388, targets := 96 }], pairs := [(1,0),(2,5),(2,6),(3,0)], upper := (rows 35 70 133 200 280 48 96 385 257), lower := (rows 35 70 133 200 280 48 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 48 113 128 256), good := (rows 98 78 206 200 376 112 96 128 256) }] }

theorem u1462 : Upper (D 9) (R 9) [34,68,129,192,264,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1462 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1463 : Route 9 := (fun mask => (mask,id))

def c1463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1463 : Upper (D 9) (R 9) [34,68,129,192,264,16,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,264,16,256] 13 (by decide) (choices 1) [1,32] r1463 c1463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u76
  · exact u77

def b1464 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 74, targets := 288 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,8),(3,0),(3,5),(3,8)], upper := (rows 35 70 133 200 280 288 65 176 304), lower := (rows 35 70 133 200 280 288 65 128 256), losses := [] }

theorem u1464 : Upper (D 9) (R 9) [34,68,129,192,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1464 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1465 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 132, targets := 256 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(2,8)], upper := (rows 35 70 133 200 280 288 80 161 289), lower := (rows 35 70 133 200 280 288 80 128 256), losses := [] }

theorem u1465 : Upper (D 9) (R 9) [34,68,129,192,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1465 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1466 : PairBound 9 := { available := 17, camps := [], pairs := [(1,0),(2,5),(3,0),(3,5),(4,5)], upper := (rows 35 70 133 200 280 288 96 145 273), lower := (rows 35 70 133 200 280 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 304 369 128 256), good := (rows 98 78 206 200 376 352 96 128 352) },{ target := 5, region := (rows 1 2 5 10 19 0 64 133 261), good := (rows 415 478 405 200 280 256 64 128 256) }] }

theorem u1466 : Upper (D 9) (R 9) [34,68,129,192,264,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1466 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1467 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 133 265 336 40 80 160 416), lower := (rows 35 70 133 265 336 40 80 128 256), losses := [] }

theorem u1467 : Upper (D 9) (R 9) [34,68,129,257,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1467 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1468 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 400, targets := 33 },{ cop := 3, region := 112, targets := 128 }], pairs := [(1,0),(4,0),(4,5),(4,7)], upper := (rows 35 70 133 265 336 40 96 144 400), lower := (rows 35 70 133 265 336 40 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 127 40 105 255 383), good := (rows 498 470 470 504 464 504 496 128 256) }] }

theorem u1468 : Upper (D 9) (R 9) [34,68,129,257,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1468 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1469 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(3,7),(4,7)], upper := (rows 35 70 133 265 336 40 192 176 304), lower := (rows 35 70 133 265 336 40 192 128 256), losses := [] }

theorem u1469 : Upper (D 9) (R 9) [34,68,129,257,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1469 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1470 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 167, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 70 133 265 336 48 72 160 416), lower := (rows 35 70 133 265 336 48 72 128 256), losses := [] }

theorem u1470 : Upper (D 9) (R 9) [34,68,129,257,320,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1470 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1471 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 396, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6)], upper := (rows 35 70 133 265 336 48 96 136 392), lower := (rows 35 70 133 265 336 48 96 128 256), losses := [] }

theorem u1471 : Upper (D 9) (R 9) [34,68,129,257,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1471 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1472 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(3,7),(4,7)], upper := (rows 35 70 133 265 336 48 192 168 296), lower := (rows 35 70 133 265 336 48 192 128 256), losses := [] }

theorem u1472 : Upper (D 9) (R 9) [34,68,129,257,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1472 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1473 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 297, targets := 128 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,7),(3,7),(4,0)], upper := (rows 35 70 133 265 400 40 80 224 352), lower := (rows 35 70 133 265 400 40 80 128 256), losses := [] }

theorem u1473 : Upper (D 9) (R 9) [34,68,129,257,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1473 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1474 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 400, targets := 33 }], pairs := [(1,0),(2,5),(4,0),(4,5)], upper := (rows 35 70 133 265 400 40 96 208 336), lower := (rows 35 70 133 265 400 40 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 127 40 105 239 367), good := (rows 498 470 470 504 400 504 496 128 256) },{ target := 5, region := (rows 1 2 5 9 83 0 64 194 322), good := (rows 415 470 157 285 400 8 464 128 256) }] }

theorem u1474 : Upper (D 9) (R 9) [34,68,129,257,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1474 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1475 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 328, targets := 128 },{ cop := 1, region := 432, targets := 1 }], pairs := [(1,7),(3,7),(4,0)], upper := (rows 35 70 133 265 400 48 72 224 352), lower := (rows 35 70 133 265 400 48 72 128 256), losses := [{ target := 7, region := (rows 1 6 4 13 16 48 79 0 257), good := (rows 363 78 335 329 304 48 72 0 256) }] }

theorem u1475 : Upper (D 9) (R 9) [34,68,129,257,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1475 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1476 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 103, targets := 256 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,8),(1,8),(2,8),(3,7)], upper := (rows 35 70 133 265 400 48 96 200 328), lower := (rows 35 70 133 265 400 48 96 128 256), losses := [] }

theorem u1476 : Upper (D 9) (R 9) [34,68,129,257,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1476 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1477 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 0, region := 404, targets := 64 }], pairs := [(1,5),(1,7),(1,8),(2,6)], upper := (rows 35 70 133 328 400 40 65 176 304), lower := (rows 35 70 133 328 400 40 65 128 256), losses := [] }

theorem u1477 : Upper (D 9) (R 9) [34,68,129,320,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1477 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1478 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 70 133 328 400 40 80 161 289), lower := (rows 35 70 133 328 400 40 80 128 256), losses := [] }

theorem u1478 : Upper (D 9) (R 9) [34,68,129,320,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1478 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1479 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6)], upper := (rows 35 70 133 328 400 40 96 145 273), lower := (rows 35 70 133 328 400 40 96 128 256), losses := [] }

theorem u1479 : Upper (D 9) (R 9) [34,68,129,320,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1479 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1480 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0)], upper := (rows 35 70 133 328 400 48 65 168 296), lower := (rows 35 70 133 328 400 48 65 128 256), losses := [] }

theorem u1480 : Upper (D 9) (R 9) [34,68,129,320,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1480 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1481 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 133 328 400 48 72 161 289), lower := (rows 35 70 133 328 400 48 72 128 256), losses := [] }

theorem u1481 : Upper (D 9) (R 9) [34,68,129,320,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1481 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1482 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 103, targets := 256 },{ cop := 4, region := 104, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 70 133 328 400 48 96 137 265), lower := (rows 35 70 133 328 400 48 96 128 256), losses := [] }

theorem u1482 : Upper (D 9) (R 9) [34,68,129,320,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1482 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1483 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 88, targets := 384 },{ cop := 3, region := 388, targets := 1 }], pairs := [(2,0),(3,7),(3,8),(4,7),(4,8)], upper := (rows 35 70 140 25 112 288 65 384 384), lower := (rows 35 70 140 25 112 288 65 128 256), losses := [] }

theorem u1483 : Upper (D 9) (R 9) [34,68,136,17,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1483 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1484 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7),(4,7)], upper := (rows 35 70 140 25 112 288 192 385 257), lower := (rows 35 70 140 25 112 288 192 128 256), losses := [] }

theorem u1484 : Upper (D 9) (R 9) [34,68,136,17,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1484 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1485 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8),(3,8)], upper := (rows 35 70 140 25 112 288 320 129 385), lower := (rows 35 70 140 25 112 288 320 128 256), losses := [] }

theorem u1485 : Upper (D 9) (R 9) [34,68,136,17,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1485 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1486 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 140 25 176 288 65 448 320), lower := (rows 35 70 140 25 176 288 65 128 256), losses := [] }

theorem u1486 : Upper (D 9) (R 9) [34,68,136,17,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1486 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1487 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,6),(0,7),(1,5),(1,7),(2,5)], upper := (rows 35 70 140 25 176 288 320 193 321), lower := (rows 35 70 140 25 176 288 320 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 352 0 128 256), good := (rows 35 39 140 25 176 288 288 128 288) }] }

theorem u1487 : Upper (D 9) (R 9) [34,68,136,17,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1487 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1488 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 420, targets := 65 },{ cop := 1, region := 432, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,6),(4,0)], upper := (rows 35 70 140 25 208 288 65 416 288), lower := (rows 35 70 140 25 208 288 65 128 256), losses := [] }

theorem u1488 : Upper (D 9) (R 9) [34,68,136,17,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1488 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1489 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 289, targets := 64 },{ cop := 3, region := 388, targets := 32 },{ cop := 3, region := 388, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,5),(2,6)], upper := (rows 35 70 140 25 208 288 96 385 257), lower := (rows 35 70 140 25 208 288 96 128 256), losses := [] }

theorem u1489 : Upper (D 9) (R 9) [34,68,136,17,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1489 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1490 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 289, targets := 64 },{ cop := 3, region := 420, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,6),(2,8)], upper := (rows 35 70 140 25 208 288 320 161 289), lower := (rows 35 70 140 25 208 288 320 128 256), losses := [{ target := 8, region := (rows 1 2 12 8 16 32 64 129 0), good := (rows 163 70 140 157 208 32 64 128 0) }] }

theorem u1490 : Upper (D 9) (R 9) [34,68,136,17,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1490 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1491 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 420, targets := 65 },{ cop := 1, region := 432, targets := 1 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(2,0),(2,6),(4,0)], upper := (rows 35 70 140 25 336 288 65 160 416), lower := (rows 35 70 140 25 336 288 65 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 73 128 256), good := (rows 67 70 206 89 336 256 65 128 256) }] }

theorem u1491 : Upper (D 9) (R 9) [34,68,136,17,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1491 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1492 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 80, targets := 129 },{ cop := 1, region := 417, targets := 64 },{ cop := 3, region := 132, targets := 32 },{ cop := 3, region := 132, targets := 64 }], pairs := [(0,6),(2,5),(2,6),(4,0),(4,7)], upper := (rows 35 70 140 25 336 288 96 129 385), lower := (rows 35 70 140 25 336 288 96 128 256), losses := [] }

theorem u1492 : Upper (D 9) (R 9) [34,68,136,17,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1492 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1493 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7),(4,7)], upper := (rows 35 70 140 25 336 288 192 161 289), lower := (rows 35 70 140 25 336 288 192 128 256), losses := [] }

theorem u1493 : Upper (D 9) (R 9) [34,68,136,17,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1493 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1494 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 432, targets := 1 }], pairs := [(0,7),(1,5),(1,7),(1,8),(4,0)], upper := (rows 35 70 140 25 400 288 65 224 352), lower := (rows 35 70 140 25 400 288 65 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 73 128 256), good := (rows 67 70 206 89 400 256 65 128 256) },{ target := 8, region := (rows 1 14 12 8 16 32 73 129 0), good := (rows 227 70 206 223 144 32 193 128 0) }] }

theorem u1494 : Upper (D 9) (R 9) [34,68,136,17,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1494 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1495 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(1,8),(2,8)], upper := (rows 35 70 140 25 400 288 96 193 321), lower := (rows 35 70 140 25 400 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 304 377 128 256), good := (rows 98 70 206 120 496 352 96 128 352) },{ target := 8, region := (rows 1 10 12 8 16 32 97 137 0), good := (rows 227 70 142 223 144 96 96 128 0) }] }

theorem u1495 : Upper (D 9) (R 9) [34,68,136,17,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1495 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1496 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,6),(4,5)], upper := (rows 35 70 140 56 208 288 65 385 257), lower := (rows 35 70 140 56 208 288 65 128 256), losses := [{ target := 6, region := (rows 3 2 20 24 16 371 0 195 323), good := (rows 419 423 140 60 444 288 417 128 288) }] }

theorem u1496 : Upper (D 9) (R 9) [34,68,136,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1496 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1497 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7),(4,5)], upper := (rows 35 70 140 56 208 288 320 129 257), lower := (rows 35 70 140 56 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 26 20 24 16 352 352 128 256), good := (rows 98 102 142 126 254 352 352 128 352) }] }

theorem u1497 : Upper (D 9) (R 9) [34,68,136,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1497 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1498 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 78, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 70 140 73 145 288 80 416 288), lower := (rows 35 70 140 73 145 288 80 128 256), losses := [] }

theorem u1498 : Upper (D 9) (R 9) [34,68,136,65,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1498 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1499 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 70 140 73 145 288 96 400 272), lower := (rows 35 70 140 73 145 288 96 128 256), losses := [] }

theorem u1499 : Upper (D 9) (R 9) [34,68,136,65,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1499 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1499
end Delivery.IrregularNine14.P09
