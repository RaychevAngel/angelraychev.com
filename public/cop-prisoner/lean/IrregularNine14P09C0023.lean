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

def b1380 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,0),(4,0)], upper := (rows 35 70 133 56 152 288 65 448 320), lower := (rows 35 70 133 56 152 288 65 128 256), losses := [] }

theorem u1380 : Upper (D 9) (R 9) [34,68,129,48,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1380 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1381 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(1,7),(2,5)], upper := (rows 35 70 133 56 152 288 320 193 321), lower := (rows 35 70 133 56 152 288 320 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 352 0 128 256), good := (rows 35 39 133 56 152 288 288 128 288) }] }

theorem u1381 : Upper (D 9) (R 9) [34,68,129,48,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1381 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1382 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 82, targets := 288 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,8),(3,0),(4,5),(4,8)], upper := (rows 35 70 133 56 208 288 65 392 264), lower := (rows 35 70 133 56 208 288 65 128 256), losses := [] }

theorem u1382 : Upper (D 9) (R 9) [34,68,129,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1382 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1383 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 388, targets := 32 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(2,5),(2,6)], upper := (rows 35 70 133 56 208 288 72 385 257), lower := (rows 35 70 133 56 208 288 72 128 256), losses := [] }

theorem u1383 : Upper (D 9) (R 9) [34,68,129,48,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1383 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1384 : PairBound 9 := { available := 9, camps := [], pairs := [(0,6),(0,7),(3,0),(3,6),(3,7)], upper := (rows 35 70 133 56 208 288 320 137 265), lower := (rows 35 70 133 56 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 352 352 128 256), good := (rows 98 102 132 120 248 352 352 128 352) },{ target := 6, region := (rows 3 2 4 24 16 352 0 128 256), good := (rows 35 39 133 56 184 288 288 128 288) },{ target := 7, region := (rows 3 2 4 24 16 352 352 0 256), good := (rows 99 103 5 120 120 352 352 0 352) }] }

theorem u1384 : Upper (D 9) (R 9) [34,68,129,48,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1384 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1385 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 90, targets := 288 }], pairs := [(1,5),(1,8),(3,5),(3,8)], upper := (rows 35 70 133 73 152 288 80 416 288), lower := (rows 35 70 133 73 152 288 80 128 256), losses := [] }

theorem u1385 : Upper (D 9) (R 9) [34,68,129,65,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1385 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1386 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 70 133 73 152 288 96 400 272), lower := (rows 35 70 133 73 152 288 96 128 256), losses := [] }

theorem u1386 : Upper (D 9) (R 9) [34,68,129,65,136,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1386 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1387 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 64 },{ cop := 3, region := 432, targets := 1 }], pairs := [(2,6),(3,5),(4,0),(4,5),(4,6)], upper := (rows 35 70 133 73 152 288 320 176 304), lower := (rows 35 70 133 73 152 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 20 0 352 128 256), good := (rows 75 86 157 73 152 320 320 128 320) }] }

theorem u1387 : Upper (D 9) (R 9) [34,68,129,65,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1387 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1388 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 74, targets := 416 }], pairs := [(1,5),(1,7),(1,8),(3,5)], upper := (rows 35 70 133 73 176 288 72 400 272), lower := (rows 35 70 133 73 176 288 72 128 256), losses := [] }

theorem u1388 : Upper (D 9) (R 9) [34,68,129,65,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1388 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1389 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 133 73 176 288 80 392 264), lower := (rows 35 70 133 73 176 288 80 128 256), losses := [] }

theorem u1389 : Upper (D 9) (R 9) [34,68,129,65,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1389 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1390 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 436, targets := 64 },{ cop := 3, region := 432, targets := 1 }], pairs := [(0,6),(2,6),(3,5),(4,0),(4,6)], upper := (rows 35 70 133 73 176 288 320 152 280), lower := (rows 35 70 133 73 176 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 16 0 352 128 256), good := (rows 75 70 141 73 208 320 320 128 320) },{ target := 6, region := (rows 3 2 12 8 24 360 0 136 264), good := (rows 35 39 133 445 176 288 288 128 288) }] }

theorem u1390 : Upper (D 9) (R 9) [34,68,129,65,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1390 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1391 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 132, targets := 256 },{ cop := 3, region := 432, targets := 1 }], pairs := [(0,6),(2,6),(2,8),(4,0)], upper := (rows 35 70 133 73 280 288 80 160 416), lower := (rows 35 70 133 73 280 288 80 128 256), losses := [] }

theorem u1391 : Upper (D 9) (R 9) [34,68,129,65,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1391 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1392 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 70 133 73 280 288 96 144 400), lower := (rows 35 70 133 73 280 288 96 128 256), losses := [] }

theorem u1392 : Upper (D 9) (R 9) [34,68,129,65,264,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1392 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1393 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 74, targets := 288 },{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7),(1,5),(1,8),(3,5),(3,8)], upper := (rows 35 70 133 73 280 288 192 176 304), lower := (rows 35 70 133 73 280 288 192 128 256), losses := [] }

theorem u1393 : Upper (D 9) (R 9) [34,68,129,65,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1393 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1394 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 74, targets := 416 }], pairs := [(1,5),(1,7),(1,8),(3,5)], upper := (rows 35 70 133 73 400 288 72 176 304), lower := (rows 35 70 133 73 400 288 72 128 256), losses := [] }

theorem u1394 : Upper (D 9) (R 9) [34,68,129,65,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1394 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1395 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 297, targets := 128 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,7),(2,6),(3,7),(4,6)], upper := (rows 35 70 133 73 400 288 80 168 296), lower := (rows 35 70 133 73 400 288 80 128 256), losses := [] }

theorem u1395 : Upper (D 9) (R 9) [34,68,129,65,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1395 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1396 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 70 133 73 400 288 96 152 280), lower := (rows 35 70 133 73 400 288 96 128 256), losses := [] }

theorem u1396 : Upper (D 9) (R 9) [34,68,129,65,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1396 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1397 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 90, targets := 288 }], pairs := [(1,5),(1,8),(3,5),(3,8),(4,5)], upper := (rows 35 70 133 88 152 288 65 416 288), lower := (rows 35 70 133 88 152 288 65 128 256), losses := [] }

theorem u1397 : Upper (D 9) (R 9) [34,68,129,80,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1397 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1398 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 388, targets := 32 }], pairs := [(0,6),(0,7),(1,7),(2,5),(2,6)], upper := (rows 35 70 133 88 152 288 96 385 257), lower := (rows 35 70 133 88 152 288 96 128 256), losses := [] }

theorem u1398 : Upper (D 9) (R 9) [34,68,129,80,136,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1398 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1399 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 132, targets := 256 }], pairs := [(0,6),(0,7),(1,7),(2,6),(2,8)], upper := (rows 35 70 133 88 152 288 320 161 289), lower := (rows 35 70 133 88 152 288 320 128 256), losses := [] }

theorem u1399 : Upper (D 9) (R 9) [34,68,129,80,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1399 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1400 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 1, region := 440, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 35 70 133 88 176 288 65 392 264), lower := (rows 35 70 133 88 176 288 65 128 256), losses := [] }

theorem u1400 : Upper (D 9) (R 9) [34,68,129,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1400 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1401 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 133 88 176 288 72 385 257), lower := (rows 35 70 133 88 176 288 72 128 256), losses := [] }

theorem u1401 : Upper (D 9) (R 9) [34,68,129,80,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1401 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1402 : PairBound 9 := { available := 9, camps := [], pairs := [(0,6),(0,7),(3,0),(3,5),(3,7)], upper := (rows 35 70 133 88 176 288 320 137 265), lower := (rows 35 70 133 88 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 352 352 128 256), good := (rows 98 102 132 120 248 352 352 128 352) },{ target := 5, region := (rows 1 2 4 24 16 0 352 128 256), good := (rows 67 70 133 88 216 320 320 128 320) },{ target := 6, region := (rows 3 2 4 8 16 352 0 128 256), good := (rows 35 39 133 56 176 288 288 128 288) },{ target := 7, region := (rows 3 2 4 24 16 352 352 0 256), good := (rows 99 103 5 120 120 352 352 0 352) }] }

theorem u1402 : Upper (D 9) (R 9) [34,68,129,80,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1402 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1403 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 4, region := 72, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 35 70 133 88 273 288 72 160 416), lower := (rows 35 70 133 88 273 288 72 128 256), losses := [] }

theorem u1403 : Upper (D 9) (R 9) [34,68,129,80,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1403 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1404 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 104, targets := 1 },{ cop := 4, region := 104, targets := 128 }], pairs := [(1,0),(1,5),(2,5),(3,0),(3,7)], upper := (rows 35 70 133 88 273 288 96 136 392), lower := (rows 35 70 133 88 273 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 312 377 152 280), good := (rows 98 70 198 504 504 352 96 128 352) },{ target := 5, region := (rows 1 10 21 10 21 0 64 139 267), good := (rows 415 478 405 478 405 256 64 128 256) }] }

theorem u1404 : Upper (D 9) (R 9) [34,68,129,80,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1404 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1405 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7),(4,7)], upper := (rows 35 70 133 88 273 288 192 168 296), lower := (rows 35 70 133 88 273 288 192 128 256), losses := [] }

theorem u1405 : Upper (D 9) (R 9) [34,68,129,80,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1405 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1406 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 133 88 400 40 65 416 288), lower := (rows 35 70 133 88 400 40 65 128 256), losses := [] }

theorem u1406 : Upper (D 9) (R 9) [34,68,129,80,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1406 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1407 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6)], upper := (rows 35 70 133 88 400 40 96 385 257), lower := (rows 35 70 133 88 400 40 96 128 256), losses := [] }

theorem u1407 : Upper (D 9) (R 9) [34,68,129,80,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1407 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1408 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 0, region := 132, targets := 64 }], pairs := [(0,8),(1,8),(2,6),(2,8)], upper := (rows 35 70 133 88 400 40 320 161 289), lower := (rows 35 70 133 88 400 40 320 128 256), losses := [] }

theorem u1408 : Upper (D 9) (R 9) [34,68,129,80,384,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1408 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1409 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0),(4,0)], upper := (rows 35 70 133 88 400 288 65 168 296), lower := (rows 35 70 133 88 400 288 65 128 256), losses := [] }

theorem u1409 : Upper (D 9) (R 9) [34,68,129,80,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1409 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1410 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(4,6)], upper := (rows 35 70 133 88 400 288 72 161 289), lower := (rows 35 70 133 88 400 288 72 128 256), losses := [] }

theorem u1410 : Upper (D 9) (R 9) [34,68,129,80,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1410 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1411 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 104, targets := 129 }], pairs := [(1,0),(2,5),(3,0),(3,5),(3,7)], upper := (rows 35 70 133 88 400 288 96 137 265), lower := (rows 35 70 133 88 400 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 304 377 128 256), good := (rows 98 70 198 120 504 352 96 128 352) },{ target := 5, region := (rows 1 2 5 10 21 0 64 129 257), good := (rows 415 94 405 88 400 256 64 128 256) }] }

theorem u1411 : Upper (D 9) (R 9) [34,68,129,80,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1411 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1412 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(1,7),(1,8),(3,7),(3,8)], upper := (rows 35 70 133 104 152 288 65 400 272), lower := (rows 35 70 133 104 152 288 65 128 256), losses := [] }

theorem u1412 : Upper (D 9) (R 9) [34,68,129,96,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1412 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1413 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 1, region := 297, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,7)], upper := (rows 35 70 133 104 152 288 80 385 257), lower := (rows 35 70 133 104 152 288 80 128 256), losses := [] }

theorem u1413 : Upper (D 9) (R 9) [34,68,129,96,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1413 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1414 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 151, targets := 256 },{ cop := 5, region := 72, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 35 70 133 104 152 288 320 145 273), lower := (rows 35 70 133 104 152 288 320 128 256), losses := [] }

theorem u1414 : Upper (D 9) (R 9) [34,68,129,96,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1414 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1415 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 133 104 273 48 72 384 384), lower := (rows 35 70 133 104 273 48 72 128 256), losses := [] }

theorem u1415 : Upper (D 9) (R 9) [34,68,129,96,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1415 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1416 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(3,7),(4,7)], upper := (rows 35 70 133 104 273 48 192 392 264), lower := (rows 35 70 133 104 273 48 192 128 256), losses := [] }

theorem u1416 : Upper (D 9) (R 9) [34,68,129,96,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1416 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1417 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 0, region := 456, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 70 133 104 273 48 320 136 392), lower := (rows 35 70 133 104 273 48 320 128 256), losses := [] }

theorem u1417 : Upper (D 9) (R 9) [34,68,129,96,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1417 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1418 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 5, region := 72, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(4,6)], upper := (rows 35 70 133 104 273 288 72 144 400), lower := (rows 35 70 133 104 273 288 72 128 256), losses := [] }

theorem u1418 : Upper (D 9) (R 9) [34,68,129,96,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1418 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1419 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 1, region := 424, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 70 133 104 273 288 80 136 392), lower := (rows 35 70 133 104 273 288 80 128 256), losses := [] }

theorem u1419 : Upper (D 9) (R 9) [34,68,129,96,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1419 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1420 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7),(4,7)], upper := (rows 35 70 133 104 273 288 192 152 280), lower := (rows 35 70 133 104 273 288 192 128 256), losses := [] }

theorem u1420 : Upper (D 9) (R 9) [34,68,129,96,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1420 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1421 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8)], upper := (rows 35 70 133 104 280 48 65 384 384), lower := (rows 35 70 133 104 280 48 65 128 256), losses := [] }

theorem u1421 : Upper (D 9) (R 9) [34,68,129,96,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1421 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1422 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 0, region := 454, targets := 32 }], pairs := [(0,7),(1,5),(3,7),(4,7)], upper := (rows 35 70 133 104 280 48 192 385 257), lower := (rows 35 70 133 104 280 48 192 128 256), losses := [] }

theorem u1422 : Upper (D 9) (R 9) [34,68,129,96,264,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1422 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1423 : PairBound 9 := { available := 129, camps := [{ cop := 6, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 35 70 133 104 280 48 320 129 385), lower := (rows 35 70 133 104 280 48 320 128 256), losses := [] }

theorem u1423 : Upper (D 9) (R 9) [34,68,129,96,264,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1423 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1424 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(1,7),(1,8),(3,7),(3,8)], upper := (rows 35 70 133 104 280 288 65 144 400), lower := (rows 35 70 133 104 280 288 65 128 256), losses := [] }

theorem u1424 : Upper (D 9) (R 9) [34,68,129,96,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1424 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1425 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 88, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 35 70 133 104 280 288 80 129 385), lower := (rows 35 70 133 104 280 288 80 128 256), losses := [] }

theorem u1425 : Upper (D 9) (R 9) [34,68,129,96,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1425 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1426 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7),(4,7)], upper := (rows 35 70 133 104 280 288 192 145 273), lower := (rows 35 70 133 104 280 288 192 128 256), losses := [] }

theorem u1426 : Upper (D 9) (R 9) [34,68,129,96,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1426 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1427 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 133 104 400 48 65 392 264), lower := (rows 35 70 133 104 400 48 65 128 256), losses := [] }

theorem u1427 : Upper (D 9) (R 9) [34,68,129,96,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1427 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1428 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 70 133 104 400 48 72 385 257), lower := (rows 35 70 133 104 400 48 72 128 256), losses := [] }

theorem u1428 : Upper (D 9) (R 9) [34,68,129,96,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1428 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1429 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 4, region := 104, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 70 133 104 400 48 320 137 265), lower := (rows 35 70 133 104 400 48 320 128 256), losses := [] }

theorem u1429 : Upper (D 9) (R 9) [34,68,129,96,384,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1429 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1430 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(1,7),(1,8),(3,7),(3,8)], upper := (rows 35 70 133 104 400 288 65 152 280), lower := (rows 35 70 133 104 400 288 65 128 256), losses := [] }

theorem u1430 : Upper (D 9) (R 9) [34,68,129,96,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1430 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1431 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 5, region := 72, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(4,6)], upper := (rows 35 70 133 104 400 288 72 145 273), lower := (rows 35 70 133 104 400 288 72 128 256), losses := [] }

theorem u1431 : Upper (D 9) (R 9) [34,68,129,96,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1431 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1432 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 1, region := 297, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8)], upper := (rows 35 70 133 104 400 288 80 137 265), lower := (rows 35 70 133 104 400 288 80 128 256), losses := [] }

theorem u1432 : Upper (D 9) (R 9) [34,68,129,96,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1432 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1433 : Route 9 := (fun mask => (mask,id))

def c1433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1433 : Upper (D 9) (R 9) [34,68,129,144,257,256,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,257,256,8] 13 (by decide) (choices 1) [32,64] r1433 c1433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u62
  · exact u63

def b1434 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(1,0),(2,5),(3,0),(3,5),(4,5)], upper := (rows 35 70 133 152 273 288 96 200 328), lower := (rows 35 70 133 152 273 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 312 377 152 280), good := (rows 98 70 198 504 504 352 96 128 352) },{ target := 5, region := (rows 1 2 5 13 17 0 64 130 258), good := (rows 415 462 157 152 285 256 64 128 256) }] }

theorem u1434 : Upper (D 9) (R 9) [34,68,129,144,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1434 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1435 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0)], upper := (rows 35 70 133 152 336 40 65 416 288), lower := (rows 35 70 133 152 336 40 65 128 256), losses := [] }

theorem u1435 : Upper (D 9) (R 9) [34,68,129,144,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1435 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1436 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 388, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8)], upper := (rows 35 70 133 152 336 40 96 385 257), lower := (rows 35 70 133 152 336 40 96 128 256), losses := [] }

theorem u1436 : Upper (D 9) (R 9) [34,68,129,144,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1436 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1437 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 133 152 336 40 320 161 289), lower := (rows 35 70 133 152 336 40 320 128 256), losses := [] }

theorem u1437 : Upper (D 9) (R 9) [34,68,129,144,320,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1437 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1438 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 416 },{ cop := 1, region := 440, targets := 1 }], pairs := [(1,5),(1,7),(1,8),(3,0),(4,0)], upper := (rows 35 70 133 152 336 288 65 168 296), lower := (rows 35 70 133 152 336 288 65 128 256), losses := [] }

theorem u1438 : Upper (D 9) (R 9) [34,68,129,144,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1438 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1439 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 1, region := 305, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,7)], upper := (rows 35 70 133 152 336 288 72 161 289), lower := (rows 35 70 133 152 336 288 72 128 256), losses := [] }

theorem u1439 : Upper (D 9) (R 9) [34,68,129,144,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1439 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1439
end Delivery.IrregularNine14.P09
