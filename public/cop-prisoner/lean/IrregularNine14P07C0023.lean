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

def b1380 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 420, targets := 3 },{ cop := 0, region := 240, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 35 268 74 145 160 80 224 352), lower := (rows 7 35 268 74 145 160 80 128 256), losses := [] }

theorem u1380 : Upper (D 7) (R 7) [6,33,264,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1380 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1381 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 405, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 268 74 145 160 96 208 336), lower := (rows 7 35 268 74 145 160 96 128 256), losses := [] }

theorem u1381 : Upper (D 7) (R 7) [6,33,264,66,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1382 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 268 74 208 160 65 176 304), lower := (rows 7 35 268 74 208 160 65 128 256), losses := [] }

theorem u1382 : Upper (D 7) (R 7) [6,33,264,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1383 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 268 74 208 160 80 161 289), lower := (rows 7 35 268 74 208 160 80 128 256), losses := [] }

theorem u1383 : Upper (D 7) (R 7) [6,33,264,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1383 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1384 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 405, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 268 74 208 160 96 145 273), lower := (rows 7 35 268 74 208 160 96 128 256), losses := [] }

theorem u1384 : Upper (D 7) (R 7) [6,33,264,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1385 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 420, targets := 3 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(3,0)], upper := (rows 7 35 268 88 145 160 66 224 352), lower := (rows 7 35 268 88 145 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 255 67 219 347), good := (rows 486 482 428 508 508 160 482 160 256) }] }

theorem u1385 : Upper (D 7) (R 7) [6,33,264,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1386 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0),(3,1)], upper := (rows 7 35 268 88 145 160 96 194 322), lower := (rows 7 35 268 88 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 179 251 131 259), good := (rows 486 482 332 124 508 224 96 224 256) }] }

theorem u1386 : Upper (D 7) (R 7) [6,33,264,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1387 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,6)], upper := (rows 7 35 268 88 176 96 65 130 386), lower := (rows 7 35 268 88 176 96 65 128 256), losses := [] }

theorem u1387 : Upper (D 7) (R 7) [6,33,264,80,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1388 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 1, region := 144, targets := 2 },{ cop := 1, region := 144, targets := 64 }], pairs := [(0,7),(1,7),(4,1),(4,6)], upper := (rows 7 35 268 88 176 96 66 129 385), lower := (rows 7 35 268 88 176 96 66 128 256), losses := [] }

theorem u1388 : Upper (D 7) (R 7) [6,33,264,80,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1389 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 35 268 88 176 96 192 131 259), lower := (rows 7 35 268 88 176 96 192 128 256), losses := [] }

theorem u1389 : Upper (D 7) (R 7) [6,33,264,80,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1390 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 268 104 81 160 66 144 400), lower := (rows 7 35 268 104 81 160 66 128 256), losses := [] }

theorem u1390 : Upper (D 7) (R 7) [6,33,264,96,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1391 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 268 104 81 160 80 130 386), lower := (rows 7 35 268 104 81 160 80 128 256), losses := [] }

theorem u1391 : Upper (D 7) (R 7) [6,33,264,96,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1391 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1392 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 268 104 81 160 192 146 274), lower := (rows 7 35 268 104 81 160 192 128 256), losses := [] }

theorem u1392 : Upper (D 7) (R 7) [6,33,264,96,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1393 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 268 104 82 160 65 144 400), lower := (rows 7 35 268 104 82 160 65 128 256), losses := [] }

theorem u1393 : Upper (D 7) (R 7) [6,33,264,96,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1394 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 88, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 7 35 268 104 82 160 80 129 385), lower := (rows 7 35 268 104 82 160 80 128 256), losses := [] }

theorem u1394 : Upper (D 7) (R 7) [6,33,264,96,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1394 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1395 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 35 268 104 82 160 192 145 273), lower := (rows 7 35 268 104 82 160 192 128 256), losses := [] }

theorem u1395 : Upper (D 7) (R 7) [6,33,264,96,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1396 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 72, targets := 129 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,7),(4,5)], upper := (rows 7 35 268 104 145 160 66 208 336), lower := (rows 7 35 268 104 145 160 66 128 256), losses := [] }

theorem u1396 : Upper (D 7) (R 7) [6,33,264,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1397 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 268 104 145 160 80 194 322), lower := (rows 7 35 268 104 145 160 80 128 256), losses := [] }

theorem u1397 : Upper (D 7) (R 7) [6,33,264,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1397 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1398 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 208, targets := 32 },{ cop := 1, region := 72, targets := 2 },{ cop := 1, region := 72, targets := 128 }], pairs := [(2,1),(3,1),(3,7),(4,5)], upper := (rows 7 35 268 104 146 160 65 208 336), lower := (rows 7 35 268 104 146 160 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 26 16 176 67 144 272), good := (rows 77 105 268 104 508 160 65 160 256) }] }

theorem u1398 : Upper (D 7) (R 7) [6,33,264,96,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1399 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 268 104 146 160 80 193 321), lower := (rows 7 35 268 104 146 160 80 128 256), losses := [] }

theorem u1399 : Upper (D 7) (R 7) [6,33,264,96,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1399 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1400 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 40, targets := 3 },{ cop := 0, region := 208, targets := 32 },{ cop := 1, region := 72, targets := 128 }], pairs := [(3,0),(3,1),(3,7),(4,5)], upper := (rows 7 35 268 104 208 160 65 146 274), lower := (rows 7 35 268 104 208 160 65 128 256), losses := [] }

theorem u1400 : Upper (D 7) (R 7) [6,33,264,96,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1401 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 72, targets := 129 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 40, targets := 2 }], pairs := [(3,0),(3,1),(3,7),(4,5)], upper := (rows 7 35 268 104 208 160 66 145 273), lower := (rows 7 35 268 104 208 160 66 128 256), losses := [] }

theorem u1401 : Upper (D 7) (R 7) [6,33,264,96,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1402 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 268 104 208 160 80 131 259), lower := (rows 7 35 268 104 208 160 80 128 256), losses := [] }

theorem u1402 : Upper (D 7) (R 7) [6,33,264,96,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1402 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1403 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 268 200 81 160 66 176 304), lower := (rows 7 35 268 200 81 160 66 128 256), losses := [] }

theorem u1403 : Upper (D 7) (R 7) [6,33,264,192,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1404 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 7 35 268 200 81 160 80 162 290), lower := (rows 7 35 268 200 81 160 80 128 256), losses := [] }

theorem u1404 : Upper (D 7) (R 7) [6,33,264,192,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1404 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1405 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 72, targets := 3 },{ cop := 1, region := 80, targets := 2 },{ cop := 1, region := 80, targets := 128 }], pairs := [(3,0),(3,1),(4,1),(4,7)], upper := (rows 7 35 268 200 81 160 96 146 274), lower := (rows 7 35 268 200 81 160 96 128 256), losses := [] }

theorem u1405 : Upper (D 7) (R 7) [6,33,264,192,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1406 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 268 200 82 48 65 160 416), lower := (rows 7 35 268 200 82 48 65 128 256), losses := [] }

theorem u1406 : Upper (D 7) (R 7) [6,33,264,192,66,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1406 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1407 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 7 35 268 200 82 48 96 129 385), lower := (rows 7 35 268 200 82 48 96 128 256), losses := [] }

theorem u1407 : Upper (D 7) (R 7) [6,33,264,192,66,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1407 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1408 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 268 200 82 48 192 161 289), lower := (rows 7 35 268 200 82 48 192 128 256), losses := [] }

theorem u1408 : Upper (D 7) (R 7) [6,33,264,192,66,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1408 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1409 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 268 200 82 160 65 176 304), lower := (rows 7 35 268 200 82 160 65 128 256), losses := [] }

theorem u1409 : Upper (D 7) (R 7) [6,33,264,192,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1410 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 268 200 82 160 80 161 289), lower := (rows 7 35 268 200 82 160 80 128 256), losses := [] }

theorem u1410 : Upper (D 7) (R 7) [6,33,264,192,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1410 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1411 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 5, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(3,5)], upper := (rows 7 35 268 200 82 160 96 145 273), lower := (rows 7 35 268 200 82 160 96 128 256), losses := [] }

theorem u1411 : Upper (D 7) (R 7) [6,33,264,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1412 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 7 35 324 25 82 160 72 160 416), lower := (rows 7 35 324 25 82 160 72 128 256), losses := [] }

theorem u1412 : Upper (D 7) (R 7) [6,33,320,17,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1412 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1413 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 88, targets := 128 }], pairs := [(0,5),(2,5),(3,5),(3,7)], upper := (rows 7 35 324 25 82 160 96 136 392), lower := (rows 7 35 324 25 82 160 96 128 256), losses := [] }

theorem u1413 : Upper (D 7) (R 7) [6,33,320,17,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1414 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(4,0)], upper := (rows 7 35 324 25 82 160 192 168 296), lower := (rows 7 35 324 25 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 232 232 136 264), good := (rows 22 114 356 508 114 224 224 224 256) }] }

theorem u1414 : Upper (D 7) (R 7) [6,33,320,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1415 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 88, targets := 128 },{ cop := 1, region := 80, targets := 1 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6),(3,7),(4,0),(4,7)], upper := (rows 7 35 324 25 112 160 66 136 392), lower := (rows 7 35 324 25 112 160 66 128 256), losses := [] }

theorem u1415 : Upper (D 7) (R 7) [6,33,320,17,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1416 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 88, targets := 2 },{ cop := 1, region := 88, targets := 128 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 7 35 324 25 112 160 72 130 386), lower := (rows 7 35 324 25 112 160 72 128 256), losses := [] }

theorem u1416 : Upper (D 7) (R 7) [6,33,320,17,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1416 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1417 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 324 25 112 160 192 138 266), lower := (rows 7 35 324 25 112 160 192 128 256), losses := [] }

theorem u1417 : Upper (D 7) (R 7) [6,33,320,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1418 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 484, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 324 25 146 160 72 224 352), lower := (rows 7 35 324 25 146 160 72 128 256), losses := [{ target := 0, region := (rows 0 2 76 8 17 253 72 204 332), good := (rows 438 50 484 508 178 160 492 160 256) }] }

theorem u1418 : Upper (D 7) (R 7) [6,33,320,17,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1418 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1419 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 484, targets := 3 }], pairs := [(0,7),(1,6),(2,0),(2,1)], upper := (rows 7 35 324 25 146 160 96 200 328), lower := (rows 7 35 324 25 146 160 96 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 16 176 0 128 256), good := (rows 7 35 260 59 178 160 32 160 256) },{ target := 7, region := (rows 17 2 20 24 16 32 98 0 272), good := (rows 71 99 324 285 351 96 96 0 256) }] }

theorem u1419 : Upper (D 7) (R 7) [6,33,320,17,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1420 : Route 9 := (fun mask => (mask,id))

def c1420 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1420 : Upper (D 7) (R 7) [6,33,320,17,192,128,2] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17,192,128,2] 13 (by decide) (choices 1) [8,32] r1420 c1420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u45
  · exact u46

def b1421 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 7 35 324 25 208 160 72 162 290), lower := (rows 7 35 324 25 208 160 72 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 187 72 131 259), good := (rows 422 418 324 508 240 160 124 160 256) }] }

theorem u1421 : Upper (D 7) (R 7) [6,33,320,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1421 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1422 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 80, targets := 3 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6),(3,1),(4,0),(4,1)], upper := (rows 7 35 324 25 208 160 96 138 266), lower := (rows 7 35 324 25 208 160 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 176 176 250 128 256), good := (rows 77 121 324 121 240 240 112 240 256) }] }

theorem u1422 : Upper (D 7) (R 7) [6,33,320,17,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1423 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 88, targets := 128 },{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(3,7),(4,7)], upper := (rows 7 35 324 26 112 160 65 136 392), lower := (rows 7 35 324 26 112 160 65 128 256), losses := [] }

theorem u1423 : Upper (D 7) (R 7) [6,33,320,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1424 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 88, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 7 35 324 26 112 160 72 129 385), lower := (rows 7 35 324 26 112 160 72 128 256), losses := [] }

theorem u1424 : Upper (D 7) (R 7) [6,33,320,18,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1424 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1425 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 324 26 112 160 192 137 265), lower := (rows 7 35 324 26 112 160 192 128 256), losses := [] }

theorem u1425 : Upper (D 7) (R 7) [6,33,320,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1426 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 468, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 35 324 26 208 40 65 160 416), lower := (rows 7 35 324 26 208 40 65 128 256), losses := [{ target := 0, region := (rows 0 2 84 9 84 107 64 255 383), good := (rows 446 426 500 446 500 424 508 128 256) }] }

theorem u1426 : Upper (D 7) (R 7) [6,33,320,18,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1426 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1427 : Route 9 := (fun mask => (mask,id))

def c1427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1427 : Upper (D 7) (R 7) [6,33,320,18,192,8,32] 13 := by
  apply FastRouting.sound _ _ [6,33,320,18,192,8,32] 13 (by decide) (choices 1) [1] r1427 c1427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u47

def b1428 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 324 26 208 40 192 161 289), lower := (rows 7 35 324 26 208 40 192 128 256), losses := [] }

theorem u1428 : Upper (D 7) (R 7) [6,33,320,18,192,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1428 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1429 : PairBound 9 := { available := 40, camps := [], pairs := [(2,0),(2,1),(3,0),(4,0)], upper := (rows 7 35 324 26 208 160 65 168 296), lower := (rows 7 35 324 26 208 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 84 9 84 255 64 203 331), good := (rows 446 426 500 446 500 160 508 160 256) },{ target := 1, region := (rows 1 0 12 8 24 184 67 136 264), good := (rows 69 97 324 508 240 160 65 160 256) }] }

theorem u1429 : Upper (D 7) (R 7) [6,33,320,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1430 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 7 35 324 26 208 160 72 161 289), lower := (rows 7 35 324 26 208 160 72 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 187 72 131 259), good := (rows 421 417 324 508 240 160 124 160 256) }] }

theorem u1430 : Upper (D 7) (R 7) [6,33,320,18,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1430 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1431 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 80, targets := 3 }], pairs := [(0,7),(3,0),(4,0),(4,1)], upper := (rows 7 35 324 26 208 160 96 137 265), lower := (rows 7 35 324 26 208 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 176 176 250 128 256), good := (rows 78 122 324 122 240 240 112 240 256) },{ target := 7, region := (rows 9 2 12 8 16 32 98 0 264), good := (rows 71 99 324 351 80 96 96 0 256) }] }

theorem u1431 : Upper (D 7) (R 7) [6,33,320,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1432 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 324 56 81 160 66 136 392), lower := (rows 7 35 324 56 81 160 66 128 256), losses := [] }

theorem u1432 : Upper (D 7) (R 7) [6,33,320,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1433 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 88, targets := 2 },{ cop := 1, region := 88, targets := 128 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 7 35 324 56 81 160 72 130 386), lower := (rows 7 35 324 56 81 160 72 128 256), losses := [] }

theorem u1433 : Upper (D 7) (R 7) [6,33,320,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1433 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1434 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6),(3,0),(3,1),(3,6)], upper := (rows 7 35 324 56 81 160 192 138 266), lower := (rows 7 35 324 56 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 6 98 356 120 120 224 224 224 256) },{ target := 1, region := (rows 1 0 4 26 18 224 224 128 256), good := (rows 29 121 356 120 121 224 224 224 256) }] }

theorem u1434 : Upper (D 7) (R 7) [6,33,320,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1435 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 324 56 82 160 65 136 392), lower := (rows 7 35 324 56 82 160 65 128 256), losses := [] }

theorem u1435 : Upper (D 7) (R 7) [6,33,320,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1436 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 88, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 7 35 324 56 82 160 72 129 385), lower := (rows 7 35 324 56 82 160 72 128 256), losses := [] }

theorem u1436 : Upper (D 7) (R 7) [6,33,320,48,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1436 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1437 : PairBound 9 := { available := 9, camps := [], pairs := [(3,0),(3,1),(4,0),(4,5)], upper := (rows 7 35 324 56 82 160 192 137 265), lower := (rows 7 35 324 56 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 26 18 224 224 128 256), good := (rows 30 122 356 120 122 224 224 224 256) },{ target := 1, region := (rows 1 0 4 24 16 224 224 128 256), good := (rows 5 97 356 120 120 224 224 224 256) },{ target := 5, region := (rows 1 2 4 8 18 0 224 128 256), good := (rows 23 83 324 88 82 192 192 192 256) }] }

theorem u1437 : Upper (D 7) (R 7) [6,33,320,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1438 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 7 35 324 73 146 160 72 176 304), lower := (rows 7 35 324 73 146 160 72 128 256), losses := [] }

theorem u1438 : Upper (D 7) (R 7) [6,33,320,65,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1438 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1439 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 420, targets := 3 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 7 35 324 73 146 160 80 168 296), lower := (rows 7 35 324 73 146 160 80 128 256), losses := [] }

theorem u1439 : Upper (D 7) (R 7) [6,33,320,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1439 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1439
end Delivery.IrregularNine14.P07
