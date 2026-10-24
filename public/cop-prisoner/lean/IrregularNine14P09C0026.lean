import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1560 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 },{ cop := 4, region := 360, targets := 128 }], pairs := [(0,6),(2,6),(3,7),(4,6),(4,8)], upper := (rows 35 70 140 328 145 288 65 176 304), lower := (rows 35 70 140 328 145 288 65 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 83 383 0 219 347), good := (rows 435 439 428 444 433 288 433 128 288) }] }

theorem u1560 : Upper (D 9) (R 9) [34,68,136,320,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1560 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1561 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 297, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 328 145 288 80 161 289), lower := (rows 35 70 140 328 145 288 80 128 256), losses := [] }

theorem u1561 : Upper (D 9) (R 9) [34,68,136,320,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1561 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1562 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 5, region := 72, targets := 129 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,6),(3,0),(3,7),(4,5),(4,6)], upper := (rows 35 70 140 328 145 288 96 145 273), lower := (rows 35 70 140 328 145 288 96 128 256), losses := [] }

theorem u1562 : Upper (D 9) (R 9) [34,68,136,320,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1562 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1563 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 115, targets := 256 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(4,6),(4,8)], upper := (rows 35 70 140 328 176 33 65 400 272), lower := (rows 35 70 140 328 176 33 65 128 256), losses := [] }

theorem u1563 : Upper (D 9) (R 9) [34,68,136,320,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1563 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1564 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 115, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(4,8)], upper := (rows 35 70 140 328 176 33 80 385 257), lower := (rows 35 70 140 328 176 33 80 128 256), losses := [] }

theorem u1564 : Upper (D 9) (R 9) [34,68,136,320,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1564 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1565 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 183, targets := 256 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 35 70 140 328 176 33 320 145 273), lower := (rows 35 70 140 328 176 33 320 128 256), losses := [] }

theorem u1565 : Upper (D 9) (R 9) [34,68,136,320,160,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1565 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1566 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 }], pairs := [(0,6),(2,6),(4,0),(4,6),(4,8)], upper := (rows 35 70 140 328 176 288 65 145 273), lower := (rows 35 70 140 328 176 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 296 64 128 256), good := (rows 34 86 188 360 176 288 64 128 288) },{ target := 6, region := (rows 3 2 12 8 95 363 0 195 323), good := (rows 435 439 188 444 176 288 433 128 288) }] }

theorem u1566 : Upper (D 9) (R 9) [34,68,136,320,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1566 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1567 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 297, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 328 176 288 80 129 257), lower := (rows 35 70 140 328 176 288 80 128 256), losses := [] }

theorem u1567 : Upper (D 9) (R 9) [34,68,136,320,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1567 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1568 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8)], upper := (rows 35 70 140 328 273 33 80 160 416), lower := (rows 35 70 140 328 273 33 80 128 256), losses := [] }

theorem u1568 : Upper (D 9) (R 9) [34,68,136,320,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1568 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1569 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 99, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 70 140 328 273 33 96 144 400), lower := (rows 35 70 140 328 273 33 96 128 256), losses := [] }

theorem u1569 : Upper (D 9) (R 9) [34,68,136,320,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1569 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1570 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 328 273 33 192 176 304), lower := (rows 35 70 140 328 273 33 192 128 256), losses := [] }

theorem u1570 : Upper (D 9) (R 9) [34,68,136,320,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1570 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1571 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 72, targets := 32 },{ cop := 4, region := 72, targets := 128 }], pairs := [(0,6),(3,5),(3,7),(4,6)], upper := (rows 35 70 140 328 273 48 65 160 416), lower := (rows 35 70 140 328 273 48 65 128 256), losses := [] }

theorem u1571 : Upper (D 9) (R 9) [34,68,136,320,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1571 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1572 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 104, targets := 129 }], pairs := [(0,6),(3,0),(3,7),(4,6)], upper := (rows 35 70 140 328 273 48 96 129 385), lower := (rows 35 70 140 328 273 48 96 128 256), losses := [] }

theorem u1572 : Upper (D 9) (R 9) [34,68,136,320,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1572 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1573 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(3,7),(4,7)], upper := (rows 35 70 140 328 273 48 192 161 289), lower := (rows 35 70 140 328 273 48 192 128 256), losses := [] }

theorem u1573 : Upper (D 9) (R 9) [34,68,136,320,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1573 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1574 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 99, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 70 140 328 304 33 65 144 400), lower := (rows 35 70 140 328 304 33 65 128 256), losses := [] }

theorem u1574 : Upper (D 9) (R 9) [34,68,136,320,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1574 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1575 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 70 140 328 304 33 80 129 385), lower := (rows 35 70 140 328 304 33 80 128 256), losses := [] }

theorem u1575 : Upper (D 9) (R 9) [34,68,136,320,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1575 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1576 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 328 304 33 192 145 273), lower := (rows 35 70 140 328 304 33 192 128 256), losses := [] }

theorem u1576 : Upper (D 9) (R 9) [34,68,136,320,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1576 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1577 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 99, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 70 140 328 400 33 65 176 304), lower := (rows 35 70 140 328 400 33 65 128 256), losses := [] }

theorem u1577 : Upper (D 9) (R 9) [34,68,136,320,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1577 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1578 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 140 328 400 33 80 161 289), lower := (rows 35 70 140 328 400 33 80 128 256), losses := [] }

theorem u1578 : Upper (D 9) (R 9) [34,68,136,320,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1578 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1579 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 99, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 70 140 328 400 33 96 145 273), lower := (rows 35 70 140 328 400 33 96 128 256), losses := [] }

theorem u1579 : Upper (D 9) (R 9) [34,68,136,320,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1579 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1580 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(2,6),(3,7),(4,6)], upper := (rows 35 70 140 328 400 48 65 161 289), lower := (rows 35 70 140 328 400 48 65 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 91 127 0 195 323), good := (rows 435 439 188 444 432 48 433 128 256) }] }

theorem u1580 : Upper (D 9) (R 9) [34,68,136,320,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1580 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1581 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 110, targets := 1 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(3,0)], upper := (rows 35 70 140 328 400 48 96 129 257), lower := (rows 35 70 140 328 400 48 96 128 256), losses := [] }

theorem u1581 : Upper (D 9) (R 9) [34,68,136,320,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1581 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1582 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 91, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 35 70 164 25 88 288 65 384 384), lower := (rows 35 70 164 25 88 288 65 128 256), losses := [] }

theorem u1582 : Upper (D 9) (R 9) [34,68,160,17,72,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1582 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1583 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 164 25 88 288 192 385 257), lower := (rows 35 70 164 25 88 288 192 128 256), losses := [] }

theorem u1583 : Upper (D 9) (R 9) [34,68,160,17,72,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1583 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1584 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 132, targets := 256 }], pairs := [(0,6),(2,6),(2,8),(3,5),(4,5)], upper := (rows 35 70 164 25 88 288 320 129 385), lower := (rows 35 70 164 25 88 288 320 128 256), losses := [] }

theorem u1584 : Upper (D 9) (R 9) [34,68,160,17,72,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1584 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1585 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 35 70 164 25 152 288 65 448 320), lower := (rows 35 70 164 25 152 288 65 128 256), losses := [] }

theorem u1585 : Upper (D 9) (R 9) [34,68,160,17,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1585 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1586 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(3,5),(4,5)], upper := (rows 35 70 164 25 152 288 320 193 321), lower := (rows 35 70 164 25 152 288 320 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 352 352 128 256), good := (rows 98 102 230 24 152 352 352 128 352) }] }

theorem u1586 : Upper (D 9) (R 9) [34,68,160,17,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1586 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1587 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 35 70 164 25 208 288 65 392 264), lower := (rows 35 70 164 25 208 288 65 128 256), losses := [] }

theorem u1587 : Upper (D 9) (R 9) [34,68,160,17,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1587 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1588 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 164 25 208 288 72 385 257), lower := (rows 35 70 164 25 208 288 72 128 256), losses := [] }

theorem u1588 : Upper (D 9) (R 9) [34,68,160,17,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1588 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1589 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 420, targets := 64 }], pairs := [(1,0),(2,0),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 25 208 288 320 137 265), lower := (rows 35 70 164 25 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 22 20 8 20 352 352 128 256), good := (rows 98 118 246 30 246 352 352 128 352) }] }

theorem u1589 : Upper (D 9) (R 9) [34,68,160,17,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1589 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1590 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 70 164 25 336 40 65 384 384), lower := (rows 35 70 164 25 336 40 65 128 256), losses := [] }

theorem u1590 : Upper (D 9) (R 9) [34,68,160,17,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1590 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1591 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(3,5),(3,7),(4,7)], upper := (rows 35 70 164 25 336 40 192 385 257), lower := (rows 35 70 164 25 336 40 192 128 256), losses := [] }

theorem u1591 : Upper (D 9) (R 9) [34,68,160,17,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1591 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1592 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 164 25 336 40 320 129 385), lower := (rows 35 70 164 25 336 40 320 128 256), losses := [] }

theorem u1592 : Upper (D 9) (R 9) [34,68,160,17,320,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1592 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1593 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 35 70 164 25 336 288 65 136 392), lower := (rows 35 70 164 25 336 288 65 128 256), losses := [] }

theorem u1593 : Upper (D 9) (R 9) [34,68,160,17,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1593 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1594 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 25 336 288 72 129 385), lower := (rows 35 70 164 25 336 288 72 128 256), losses := [] }

theorem u1594 : Upper (D 9) (R 9) [34,68,160,17,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1594 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1595 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(3,5),(3,7),(4,5),(4,7)], upper := (rows 35 70 164 25 336 288 192 137 265), lower := (rows 35 70 164 25 336 288 192 128 256), losses := [] }

theorem u1595 : Upper (D 9) (R 9) [34,68,160,17,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1595 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1596 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 35 70 164 25 400 288 65 200 328), lower := (rows 35 70 164 25 400 288 65 128 256), losses := [] }

theorem u1596 : Upper (D 9) (R 9) [34,68,160,17,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1596 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1597 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 25 400 288 72 193 321), lower := (rows 35 70 164 25 400 288 72 128 256), losses := [] }

theorem u1597 : Upper (D 9) (R 9) [34,68,160,17,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1597 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1598 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 164 73 152 288 65 400 272), lower := (rows 35 70 164 73 152 288 65 128 256), losses := [] }

theorem u1598 : Upper (D 9) (R 9) [34,68,160,65,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1598 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1599 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 164 73 152 288 80 385 257), lower := (rows 35 70 164 73 152 288 80 128 256), losses := [] }

theorem u1599 : Upper (D 9) (R 9) [34,68,160,65,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1599 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1600 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 },{ cop := 3, region := 144, targets := 256 }], pairs := [(2,6),(3,5),(4,5),(4,6),(4,8)], upper := (rows 35 70 164 73 152 288 320 145 273), lower := (rows 35 70 164 73 152 288 320 128 256), losses := [] }

theorem u1600 : Upper (D 9) (R 9) [34,68,160,65,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1600 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1601 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 35 70 164 73 280 288 65 144 400), lower := (rows 35 70 164 73 280 288 65 128 256), losses := [] }

theorem u1601 : Upper (D 9) (R 9) [34,68,160,65,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1601 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1602 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 73 280 288 80 129 385), lower := (rows 35 70 164 73 280 288 80 128 256), losses := [] }

theorem u1602 : Upper (D 9) (R 9) [34,68,160,65,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1602 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1603 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 67, targets := 256 }], pairs := [(0,7),(0,8),(1,8),(3,7),(4,7)], upper := (rows 35 70 164 73 280 288 192 145 273), lower := (rows 35 70 164 73 280 288 192 128 256), losses := [] }

theorem u1603 : Upper (D 9) (R 9) [34,68,160,65,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1603 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1604 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 91, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 35 70 164 88 145 288 65 392 264), lower := (rows 35 70 164 88 145 288 65 128 256), losses := [] }

theorem u1604 : Upper (D 9) (R 9) [34,68,160,80,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1604 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1605 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 91, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 164 88 145 288 72 385 257), lower := (rows 35 70 164 88 145 288 72 128 256), losses := [] }

theorem u1605 : Upper (D 9) (R 9) [34,68,160,80,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1605 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1606 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 328, targets := 128 }], pairs := [(1,0),(1,5),(3,5),(3,7),(4,5)], upper := (rows 35 70 164 88 145 288 320 137 265), lower := (rows 35 70 164 88 145 288 320 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 352 352 128 256), good := (rows 98 102 230 120 144 352 352 128 352) },{ target := 5, region := (rows 1 6 4 25 17 0 377 145 273), good := (rows 475 70 198 472 473 320 320 128 320) }] }

theorem u1606 : Upper (D 9) (R 9) [34,68,160,80,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1606 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1607 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 35 70 164 88 273 288 65 136 392), lower := (rows 35 70 164 88 273 288 65 128 256), losses := [] }

theorem u1607 : Upper (D 9) (R 9) [34,68,160,80,257,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1607 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1608 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 437, targets := 64 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 35 70 164 88 273 288 72 129 385), lower := (rows 35 70 164 88 273 288 72 128 256), losses := [] }

theorem u1608 : Upper (D 9) (R 9) [34,68,160,80,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1608 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1609 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(3,5),(3,7),(4,5),(4,7)], upper := (rows 35 70 164 88 273 288 192 137 265), lower := (rows 35 70 164 88 273 288 192 128 256), losses := [] }

theorem u1609 : Upper (D 9) (R 9) [34,68,160,80,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1609 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1610 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 35 70 164 137 273 288 72 208 336), lower := (rows 35 70 164 137 273 288 72 128 256), losses := [] }

theorem u1610 : Upper (D 9) (R 9) [34,68,160,129,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1610 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1611 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 336, targets := 128 },{ cop := 4, region := 200, targets := 256 }], pairs := [(3,5),(3,8),(4,5),(4,7)], upper := (rows 35 70 164 137 273 288 80 200 328), lower := (rows 35 70 164 137 273 288 80 128 256), losses := [] }

theorem u1611 : Upper (D 9) (R 9) [34,68,160,129,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1611 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1612 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 35 70 164 137 280 288 65 208 336), lower := (rows 35 70 164 137 280 288 65 128 256), losses := [] }

theorem u1612 : Upper (D 9) (R 9) [34,68,160,129,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1612 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1613 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 289, targets := 128 },{ cop := 3, region := 336, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,7)], upper := (rows 35 70 164 137 280 288 80 193 321), lower := (rows 35 70 164 137 280 288 80 128 256), losses := [] }

theorem u1613 : Upper (D 9) (R 9) [34,68,160,129,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1613 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1614 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 35 70 164 137 336 288 65 152 280), lower := (rows 35 70 164 137 336 288 65 128 256), losses := [] }

theorem u1614 : Upper (D 9) (R 9) [34,68,160,129,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1614 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1615 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 35 70 164 137 336 288 72 145 273), lower := (rows 35 70 164 137 336 288 72 128 256), losses := [] }

theorem u1615 : Upper (D 9) (R 9) [34,68,160,129,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1615 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1616 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 0, region := 136, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(3,6)], upper := (rows 35 70 164 137 336 288 80 137 265), lower := (rows 35 70 164 137 336 288 80 128 256), losses := [] }

theorem u1616 : Upper (D 9) (R 9) [34,68,160,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1616 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1617 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 35 70 164 152 336 288 65 137 265), lower := (rows 35 70 164 152 336 288 65 128 256), losses := [] }

theorem u1617 : Upper (D 9) (R 9) [34,68,160,144,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1617 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1618 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 152 336 288 72 129 257), lower := (rows 35 70 164 152 336 288 72 128 256), losses := [] }

theorem u1618 : Upper (D 9) (R 9) [34,68,160,144,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1618 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1619 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 35 70 164 200 273 48 65 392 264), lower := (rows 35 70 164 200 273 48 65 128 256), losses := [] }

theorem u1619 : Upper (D 9) (R 9) [34,68,160,192,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1619 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1619
end Delivery.IrregularNine14.P09
