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

def b1500 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 },{ cop := 3, region := 436, targets := 64 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,6),(2,6),(3,7),(4,6),(4,8)], upper := (rows 35 70 140 73 145 288 320 176 304), lower := (rows 35 70 140 73 145 288 320 128 256), losses := [] }

theorem u1500 : Upper (D 9) (R 9) [34,68,136,65,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1500 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1501 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 3, region := 438, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8),(3,8)], upper := (rows 35 70 140 73 176 288 65 400 272), lower := (rows 35 70 140 73 176 288 65 128 256), losses := [] }

theorem u1501 : Upper (D 9) (R 9) [34,68,136,65,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1501 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1502 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 140 73 176 288 80 385 257), lower := (rows 35 70 140 73 176 288 80 128 256), losses := [] }

theorem u1502 : Upper (D 9) (R 9) [34,68,136,65,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1502 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1503 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 },{ cop := 3, region := 436, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,6),(4,8)], upper := (rows 35 70 140 73 176 288 320 145 273), lower := (rows 35 70 140 73 176 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 16 0 352 128 256), good := (rows 75 70 140 73 208 320 320 128 320) }] }

theorem u1503 : Upper (D 9) (R 9) [34,68,136,65,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1503 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1504 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 3, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(2,0),(4,6)], upper := (rows 35 70 140 73 273 288 80 160 416), lower := (rows 35 70 140 73 273 288 80 128 256), losses := [] }

theorem u1504 : Upper (D 9) (R 9) [34,68,136,65,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1504 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1505 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 70 140 73 273 288 96 144 400), lower := (rows 35 70 140 73 273 288 96 128 256), losses := [] }

theorem u1505 : Upper (D 9) (R 9) [34,68,136,65,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1505 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1506 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7),(4,7)], upper := (rows 35 70 140 73 273 288 192 176 304), lower := (rows 35 70 140 73 273 288 192 128 256), losses := [] }

theorem u1506 : Upper (D 9) (R 9) [34,68,136,65,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1506 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1507 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 416 },{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(3,7),(3,8)], upper := (rows 35 70 140 73 400 288 65 176 304), lower := (rows 35 70 140 73 400 288 65 128 256), losses := [] }

theorem u1507 : Upper (D 9) (R 9) [34,68,136,65,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1507 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1508 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 297, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 73 400 288 80 161 289), lower := (rows 35 70 140 73 400 288 80 128 256), losses := [] }

theorem u1508 : Upper (D 9) (R 9) [34,68,136,65,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1508 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1509 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 70 140 73 400 288 96 145 273), lower := (rows 35 70 140 73 400 288 96 128 256), losses := [] }

theorem u1509 : Upper (D 9) (R 9) [34,68,136,65,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1509 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1510 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 140 88 176 288 65 385 257), lower := (rows 35 70 140 88 176 288 65 128 256), losses := [] }

theorem u1510 : Upper (D 9) (R 9) [34,68,136,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1510 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1511 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 144, targets := 256 }], pairs := [(0,6),(0,7),(1,7),(4,6),(4,8)], upper := (rows 35 70 140 88 176 288 320 129 257), lower := (rows 35 70 140 88 176 288 320 128 256), losses := [] }

theorem u1511 : Upper (D 9) (R 9) [34,68,136,80,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1511 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1512 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(2,6),(4,6)], upper := (rows 35 70 140 88 400 288 65 161 289), lower := (rows 35 70 140 88 400 288 65 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 91 379 0 195 323), good := (rows 435 439 188 444 432 288 433 128 288) }] }

theorem u1512 : Upper (D 9) (R 9) [34,68,136,80,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1512 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1513 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 110, targets := 1 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(3,0),(4,6)], upper := (rows 35 70 140 88 400 288 96 129 257), lower := (rows 35 70 140 88 400 288 96 128 256), losses := [] }

theorem u1513 : Upper (D 9) (R 9) [34,68,136,80,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1513 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1514 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 72, targets := 384 },{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(3,7),(3,8),(4,5),(4,6)], upper := (rows 35 70 140 104 145 288 65 400 272), lower := (rows 35 70 140 104 145 288 65 128 256), losses := [] }

theorem u1514 : Upper (D 9) (R 9) [34,68,136,96,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1514 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1515 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 297, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 104 145 288 80 385 257), lower := (rows 35 70 140 104 145 288 80 128 256), losses := [] }

theorem u1515 : Upper (D 9) (R 9) [34,68,136,96,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1515 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1516 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 151, targets := 256 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 140 104 145 288 320 145 273), lower := (rows 35 70 140 104 145 288 320 128 256), losses := [] }

theorem u1516 : Upper (D 9) (R 9) [34,68,136,96,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1516 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1517 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 140 104 273 48 65 384 384), lower := (rows 35 70 140 104 273 48 65 128 256), losses := [] }

theorem u1517 : Upper (D 9) (R 9) [34,68,136,96,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1517 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1518 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(3,7),(4,7)], upper := (rows 35 70 140 104 273 48 192 385 257), lower := (rows 35 70 140 104 273 48 192 128 256), losses := [] }

theorem u1518 : Upper (D 9) (R 9) [34,68,136,96,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1518 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1519 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8)], upper := (rows 35 70 140 104 273 48 320 129 385), lower := (rows 35 70 140 104 273 48 320 128 256), losses := [] }

theorem u1519 : Upper (D 9) (R 9) [34,68,136,96,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1519 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1520 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 384 },{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(3,7),(3,8),(4,5),(4,6)], upper := (rows 35 70 140 104 273 288 65 144 400), lower := (rows 35 70 140 104 273 288 65 128 256), losses := [] }

theorem u1520 : Upper (D 9) (R 9) [34,68,136,96,257,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1520 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1521 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8)], upper := (rows 35 70 140 104 273 288 80 129 385), lower := (rows 35 70 140 104 273 288 80 128 256), losses := [] }

theorem u1521 : Upper (D 9) (R 9) [34,68,136,96,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1521 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1522 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7),(4,7)], upper := (rows 35 70 140 104 273 288 192 145 273), lower := (rows 35 70 140 104 273 288 192 128 256), losses := [] }

theorem u1522 : Upper (D 9) (R 9) [34,68,136,96,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1522 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1523 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 72, targets := 384 },{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(3,7),(3,8),(4,5),(4,6)], upper := (rows 35 70 140 104 400 288 65 145 273), lower := (rows 35 70 140 104 400 288 65 128 256), losses := [] }

theorem u1523 : Upper (D 9) (R 9) [34,68,136,96,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1523 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1524 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 4, region := 110, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8)], upper := (rows 35 70 140 104 400 288 80 129 257), lower := (rows 35 70 140 104 400 288 80 128 256), losses := [] }

theorem u1524 : Upper (D 9) (R 9) [34,68,136,96,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1524 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1525 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 80, targets := 128 },{ cop := 0, region := 80, targets := 256 },{ cop := 1, region := 432, targets := 1 }], pairs := [(1,5),(2,0),(4,0),(4,7),(4,8)], upper := (rows 35 70 140 265 112 288 65 144 400), lower := (rows 35 70 140 265 112 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 82 379 64 211 339), good := (rows 434 502 172 428 496 288 496 128 288) },{ target := 5, region := (rows 1 6 4 8 16 0 73 144 272), good := (rows 67 70 206 329 464 256 65 128 256) }] }

theorem u1525 : Upper (D 9) (R 9) [34,68,136,257,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1525 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1526 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 5, region := 80, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 35 70 140 265 112 288 80 129 385), lower := (rows 35 70 140 265 112 288 80 128 256), losses := [] }

theorem u1526 : Upper (D 9) (R 9) [34,68,136,257,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1526 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1527 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7),(4,7)], upper := (rows 35 70 140 265 112 288 192 145 273), lower := (rows 35 70 140 265 112 288 192 128 256), losses := [] }

theorem u1527 : Upper (D 9) (R 9) [34,68,136,257,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1527 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1528 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 115, targets := 256 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,8),(1,8),(3,7),(4,8)], upper := (rows 35 70 140 265 145 48 96 448 320), lower := (rows 35 70 140 265 145 48 96 128 256), losses := [] }

theorem u1528 : Upper (D 9) (R 9) [34,68,136,257,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1528 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1529 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 177, targets := 256 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,8),(1,0),(3,7),(4,8)], upper := (rows 35 70 140 265 145 48 320 224 352), lower := (rows 35 70 140 265 145 48 320 128 256), losses := [{ target := 0, region := (rows 0 14 12 8 16 48 377 177 305), good := (rows 482 70 206 462 496 496 320 128 320) }] }

theorem u1529 : Upper (D 9) (R 9) [34,68,136,257,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1529 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1530 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 297, targets := 128 },{ cop := 0, region := 208, targets := 256 }], pairs := [(0,7),(1,8),(3,7),(4,8)], upper := (rows 35 70 140 265 145 288 80 224 352), lower := (rows 35 70 140 265 145 288 80 128 256), losses := [{ target := 8, region := (rows 1 14 12 8 25 32 93 129 0), good := (rows 243 70 222 223 209 32 80 128 0) }] }

theorem u1530 : Upper (D 9) (R 9) [34,68,136,257,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1530 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1531 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 208, targets := 256 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(3,7),(4,8)], upper := (rows 35 70 140 265 145 288 96 208 336), lower := (rows 35 70 140 265 145 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 312 381 144 272), good := (rows 98 70 238 360 496 352 96 128 352) },{ target := 7, region := (rows 5 6 4 24 16 312 381 0 272), good := (rows 99 71 111 361 377 352 96 0 352) }] }

theorem u1531 : Upper (D 9) (R 9) [34,68,136,257,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1531 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1532 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 115, targets := 256 },{ cop := 0, region := 396, targets := 64 }], pairs := [(0,8),(1,8),(2,6),(4,8)], upper := (rows 35 70 140 265 208 48 65 416 288), lower := (rows 35 70 140 265 208 48 65 128 256), losses := [] }

theorem u1532 : Upper (D 9) (R 9) [34,68,136,257,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1532 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1533 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 396, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6)], upper := (rows 35 70 140 265 208 48 96 385 257), lower := (rows 35 70 140 265 208 48 96 128 256), losses := [] }

theorem u1533 : Upper (D 9) (R 9) [34,68,136,257,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1533 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1534 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 177, targets := 256 }], pairs := [(0,8),(2,6),(3,6),(4,8)], upper := (rows 35 70 140 265 208 48 320 161 289), lower := (rows 35 70 140 265 208 48 320 128 256), losses := [] }

theorem u1534 : Upper (D 9) (R 9) [34,68,136,257,192,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1534 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1535 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 208, targets := 256 },{ cop := 1, region := 432, targets := 1 }], pairs := [(1,5),(2,0),(4,0),(4,5),(4,8)], upper := (rows 35 70 140 265 208 288 65 176 304), lower := (rows 35 70 140 265 208 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 82 379 64 211 339), good := (rows 434 502 172 428 496 288 496 128 288) },{ target := 5, region := (rows 1 6 4 8 20 0 73 128 256), good := (rows 67 86 222 329 208 256 65 128 256) }] }

theorem u1535 : Upper (D 9) (R 9) [34,68,136,257,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1535 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1536 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 82, targets := 289 }], pairs := [(1,0),(1,5),(1,8),(4,0)], upper := (rows 35 70 140 265 208 288 80 161 289), lower := (rows 35 70 140 265 208 288 80 128 256), losses := [] }

theorem u1536 : Upper (D 9) (R 9) [34,68,136,257,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1536 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1537 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 256 }], pairs := [(0,7),(1,0),(1,7),(4,0),(4,8)], upper := (rows 35 70 140 265 208 288 96 145 273), lower := (rows 35 70 140 265 208 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 20 296 365 128 256), good := (rows 98 86 254 360 208 352 96 128 352) },{ target := 7, region := (rows 5 6 4 8 16 296 365 0 256), good := (rows 99 71 111 361 80 352 96 0 352) }] }

theorem u1537 : Upper (D 9) (R 9) [34,68,136,257,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1537 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1538 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 2, region := 99, targets := 256 },{ cop := 1, region := 432, targets := 1 }], pairs := [(0,8),(1,8),(3,7),(4,0),(4,7)], upper := (rows 35 70 140 265 336 160 65 176 304), lower := (rows 35 70 140 265 336 160 65 128 256), losses := [] }

theorem u1538 : Upper (D 9) (R 9) [34,68,136,257,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1538 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1539 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 3, region := 80, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 35 70 140 265 336 160 80 161 289), lower := (rows 35 70 140 265 336 160 80 128 256), losses := [] }

theorem u1539 : Upper (D 9) (R 9) [34,68,136,257,320,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1539 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1540 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 2, region := 99, targets := 256 },{ cop := 2, region := 98, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(3,7),(4,7)], upper := (rows 35 70 140 265 336 160 96 145 273), lower := (rows 35 70 140 265 336 160 96 128 256), losses := [] }

theorem u1540 : Upper (D 9) (R 9) [34,68,136,257,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1540 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1541 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 328, targets := 128 },{ cop := 1, region := 432, targets := 1 }], pairs := [(1,5),(1,7),(3,7),(4,0)], upper := (rows 35 70 140 265 400 48 65 224 352), lower := (rows 35 70 140 265 400 48 65 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 73 128 256), good := (rows 67 70 206 329 400 16 65 128 256) },{ target := 7, region := (rows 1 6 4 73 16 48 73 0 257), good := (rows 363 78 78 329 304 48 329 0 256) }] }

theorem u1541 : Upper (D 9) (R 9) [34,68,136,257,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1541 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1542 : Route 9 := (fun mask => (mask,id))

def c1542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1542 : Upper (D 9) (R 9) [34,68,136,257,384,16,32] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,384,16,32] 13 (by decide) (choices 1) [1,64] r1542 c1542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u78
  · exact u79

def b1543 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 6, region := 16, targets := 160 }], pairs := [(1,0),(2,0),(3,0),(4,5),(4,7)], upper := (rows 35 70 140 280 81 288 65 160 416), lower := (rows 35 70 140 280 81 288 65 128 256), losses := [] }

theorem u1543 : Upper (D 9) (R 9) [34,68,136,272,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1543 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1544 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 4, region := 396, targets := 64 }], pairs := [(1,5),(2,5),(2,6),(3,5),(3,6)], upper := (rows 35 70 140 280 81 288 96 129 385), lower := (rows 35 70 140 280 81 288 96 128 256), losses := [] }

theorem u1544 : Upper (D 9) (R 9) [34,68,136,272,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1544 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1545 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7),(4,7)], upper := (rows 35 70 140 280 81 288 192 161 289), lower := (rows 35 70 140 280 81 288 192 128 256), losses := [] }

theorem u1545 : Upper (D 9) (R 9) [34,68,136,272,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1545 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1546 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 80, targets := 128 },{ cop := 0, region := 80, targets := 256 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,5),(2,5),(4,7),(4,8)], upper := (rows 35 70 140 280 112 288 65 129 385), lower := (rows 35 70 140 280 112 288 65 128 256), losses := [{ target := 5, region := (rows 1 18 20 24 16 0 65 193 321), good := (rows 451 454 140 286 478 256 449 128 256) }] }

theorem u1546 : Upper (D 9) (R 9) [34,68,136,272,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1546 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1547 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7),(4,7)], upper := (rows 35 70 140 280 112 288 192 129 257), lower := (rows 35 70 140 280 112 288 192 128 256), losses := [] }

theorem u1547 : Upper (D 9) (R 9) [34,68,136,272,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1547 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1548 : Route 9 := (fun mask => (mask,id))

def c1548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1548 : Upper (D 9) (R 9) [34,68,136,272,129,256,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,272,129,256,1] 13 (by decide) (choices 1) [32,64] r1548 c1548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u80
  · exact u81

def b1549 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 208, targets := 256 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(3,7),(4,8)], upper := (rows 35 70 140 280 145 288 96 193 321), lower := (rows 35 70 140 280 145 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 296 365 128 256), good := (rows 98 70 238 376 208 352 96 128 352) }] }

theorem u1549 : Upper (D 9) (R 9) [34,68,136,272,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1549 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1550 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 115, targets := 256 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,8)], upper := (rows 35 70 140 280 208 33 65 416 288), lower := (rows 35 70 140 280 208 33 65 128 256), losses := [] }

theorem u1550 : Upper (D 9) (R 9) [34,68,136,272,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1550 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1551 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 115, targets := 256 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,8)], upper := (rows 35 70 140 280 208 33 96 385 257), lower := (rows 35 70 140 280 208 33 96 128 256), losses := [] }

theorem u1551 : Upper (D 9) (R 9) [34,68,136,272,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1551 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1552 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 177, targets := 256 },{ cop := 2, region := 355, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,7),(4,8)], upper := (rows 35 70 140 280 208 33 320 161 289), lower := (rows 35 70 140 280 208 33 320 128 256), losses := [] }

theorem u1552 : Upper (D 9) (R 9) [34,68,136,272,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1552 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1553 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 208, targets := 256 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,6),(4,8)], upper := (rows 35 70 140 280 208 288 65 161 289), lower := (rows 35 70 140 280 208 288 65 128 256), losses := [{ target := 6, region := (rows 3 2 20 24 16 379 0 195 323), good := (rows 419 423 172 316 444 288 417 128 288) }] }

theorem u1553 : Upper (D 9) (R 9) [34,68,136,272,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1553 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1554 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 208, targets := 256 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(1,0),(1,7),(4,8)], upper := (rows 35 70 140 280 208 288 96 129 257), lower := (rows 35 70 140 280 208 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 20 296 365 128 256), good := (rows 98 86 254 376 208 352 96 128 352) }] }

theorem u1554 : Upper (D 9) (R 9) [34,68,136,272,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1554 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1555 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 115, targets := 256 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,8),(1,8),(4,5),(4,8)], upper := (rows 35 70 140 296 145 48 65 448 320), lower := (rows 35 70 140 296 145 48 65 128 256), losses := [] }

theorem u1555 : Upper (D 9) (R 9) [34,68,136,288,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1555 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1556 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 177, targets := 256 },{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,8),(3,7),(4,5),(4,8)], upper := (rows 35 70 140 296 145 48 320 193 321), lower := (rows 35 70 140 296 145 48 320 128 256), losses := [] }

theorem u1556 : Upper (D 9) (R 9) [34,68,136,288,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1556 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1557 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 115, targets := 256 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(4,8)], upper := (rows 35 70 140 328 145 48 65 416 288), lower := (rows 35 70 140 328 145 48 65 128 256), losses := [] }

theorem u1557 : Upper (D 9) (R 9) [34,68,136,320,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1557 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1558 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 115, targets := 256 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(4,8)], upper := (rows 35 70 140 328 145 48 96 385 257), lower := (rows 35 70 140 328 145 48 96 128 256), losses := [] }

theorem u1558 : Upper (D 9) (R 9) [34,68,136,320,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1558 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1559 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 183, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 140 328 145 48 320 161 289), lower := (rows 35 70 140 328 145 48 320 128 256), losses := [] }

theorem u1559 : Upper (D 9) (R 9) [34,68,136,320,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1559 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1559
end Delivery.IrregularNine14.P09
