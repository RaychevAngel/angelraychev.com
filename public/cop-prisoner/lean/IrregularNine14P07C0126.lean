import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0009

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7560 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,1)], upper := (rows 37 98 13 392 81 34 192 146 274), lower := (rows 37 98 13 392 81 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 32 200 128 256), good := (rows 53 96 93 456 81 32 192 192 256) }] }

theorem u7560 : Upper (D 7) (R 7) [36,96,9,384,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7561 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 13 392 145 34 66 208 336), lower := (rows 37 98 13 392 145 34 66 128 256), losses := [] }

theorem u7561 : Upper (D 7) (R 7) [36,96,9,384,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7562 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 98 13 392 145 34 80 194 322), lower := (rows 37 98 13 392 145 34 80 128 256), losses := [] }

theorem u7562 : Upper (D 7) (R 7) [36,96,9,384,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7562 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7563 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 392 146 34 65 208 336), lower := (rows 37 98 13 392 146 34 65 128 256), losses := [] }

theorem u7563 : Upper (D 7) (R 7) [36,96,9,384,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7564 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 13 392 146 34 80 193 321), lower := (rows 37 98 13 392 146 34 80 128 256), losses := [] }

theorem u7564 : Upper (D 7) (R 7) [36,96,9,384,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7564 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7565 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 13 392 146 48 65 194 322), lower := (rows 37 98 13 392 146 48 65 128 256), losses := [] }

theorem u7565 : Upper (D 7) (R 7) [36,96,9,384,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7565 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7566 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 13 392 146 48 66 193 321), lower := (rows 37 98 13 392 146 48 66 128 256), losses := [] }

theorem u7566 : Upper (D 7) (R 7) [36,96,9,384,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7566 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7567 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 392 208 34 65 146 274), lower := (rows 37 98 13 392 208 34 65 128 256), losses := [] }

theorem u7567 : Upper (D 7) (R 7) [36,96,9,384,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7568 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 13 392 208 34 66 145 273), lower := (rows 37 98 13 392 208 34 66 128 256), losses := [] }

theorem u7568 : Upper (D 7) (R 7) [36,96,9,384,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7569 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 13 392 208 34 80 131 259), lower := (rows 37 98 13 392 208 34 80 128 256), losses := [] }

theorem u7569 : Upper (D 7) (R 7) [36,96,9,384,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7569 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7570 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 14 25 208 288 65 130 386), lower := (rows 37 98 14 25 208 288 65 128 256), losses := [] }

theorem u7570 : Upper (D 7) (R 7) [36,96,10,17,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7570 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7571 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 417, targets := 66 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(1,0)], upper := (rows 37 98 14 25 208 288 66 129 385), lower := (rows 37 98 14 25 208 288 66 128 256), losses := [] }

theorem u7571 : Upper (D 7) (R 7) [36,96,10,17,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7571 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7572 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 14 25 208 288 192 131 259), lower := (rows 37 98 14 25 208 288 192 128 256), losses := [] }

theorem u7572 : Upper (D 7) (R 7) [36,96,10,17,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7572 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7573 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 66, targets := 128 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 37 98 14 25 274 160 65 192 448), lower := (rows 37 98 14 25 274 160 65 128 256), losses := [] }

theorem u7573 : Upper (D 7) (R 7) [36,96,10,17,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7574 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 14 25 274 160 192 193 321), lower := (rows 37 98 14 25 274 160 192 128 256), losses := [] }

theorem u7574 : Upper (D 7) (R 7) [36,96,10,17,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7575 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 66, targets := 128 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 37 98 14 25 336 160 65 130 386), lower := (rows 37 98 14 25 336 160 65 128 256), losses := [] }

theorem u7575 : Upper (D 7) (R 7) [36,96,10,17,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7576 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 5, region := 66, targets := 129 }], pairs := [(0,1),(0,6),(1,0),(1,7)], upper := (rows 37 98 14 25 336 160 66 129 385), lower := (rows 37 98 14 25 336 160 66 128 256), losses := [] }

theorem u7576 : Upper (D 7) (R 7) [36,96,10,17,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7577 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 14 25 336 160 192 131 259), lower := (rows 37 98 14 25 336 160 192 128 256), losses := [] }

theorem u7577 : Upper (D 7) (R 7) [36,96,10,17,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7578 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 66, targets := 128 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 37 98 14 25 400 160 65 194 322), lower := (rows 37 98 14 25 400 160 65 128 256), losses := [] }

theorem u7578 : Upper (D 7) (R 7) [36,96,10,17,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7579 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(3,5)], upper := (rows 37 98 14 25 400 160 66 193 321), lower := (rows 37 98 14 25 400 160 66 128 256), losses := [{ target := 0, region := (rows 0 187 12 8 16 176 255 128 256), good := (rows 102 98 78 126 498 226 66 226 256) },{ target := 5, region := (rows 1 2 4 9 25 0 70 129 257), good := (rows 477 66 94 409 400 128 66 128 256) }] }

theorem u7579 : Upper (D 7) (R 7) [36,96,10,17,384,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7580 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 98 14 88 145 288 65 130 386), lower := (rows 37 98 14 88 145 288 65 128 256), losses := [] }

theorem u7580 : Upper (D 7) (R 7) [36,96,10,80,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7580 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7581 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 14 88 145 288 66 129 385), lower := (rows 37 98 14 88 145 288 66 128 256), losses := [] }

theorem u7581 : Upper (D 7) (R 7) [36,96,10,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7581 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7582 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 14 88 145 288 192 131 259), lower := (rows 37 98 14 88 145 288 192 128 256), losses := [] }

theorem u7582 : Upper (D 7) (R 7) [36,96,10,80,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7582 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7583 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 72, targets := 162 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(3,5),(3,7)], upper := (rows 37 98 14 88 273 160 65 130 386), lower := (rows 37 98 14 88 273 160 65 128 256), losses := [] }

theorem u7583 : Upper (D 7) (R 7) [36,96,10,80,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7584 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 14 88 273 160 66 129 385), lower := (rows 37 98 14 88 273 160 66 128 256), losses := [] }

theorem u7584 : Upper (D 7) (R 7) [36,96,10,80,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7585 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 14 88 273 160 192 131 259), lower := (rows 37 98 14 88 273 160 192 128 256), losses := [] }

theorem u7585 : Upper (D 7) (R 7) [36,96,10,80,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7586 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(1,7),(4,6)], upper := (rows 37 98 14 88 274 160 65 129 385), lower := (rows 37 98 14 88 274 160 65 128 256), losses := [] }

theorem u7586 : Upper (D 7) (R 7) [36,96,10,80,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7587 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 14 88 274 160 192 129 257), lower := (rows 37 98 14 88 274 160 192 128 256), losses := [] }

theorem u7587 : Upper (D 7) (R 7) [36,96,10,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7588 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 136, targets := 2 }], pairs := [(1,7),(3,1),(4,7)], upper := (rows 37 98 14 137 81 288 66 144 400), lower := (rows 37 98 14 137 81 288 66 128 256), losses := [] }

theorem u7588 : Upper (D 7) (R 7) [36,96,10,129,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7588 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7589 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 14 137 81 288 80 130 386), lower := (rows 37 98 14 137 81 288 80 128 256), losses := [] }

theorem u7589 : Upper (D 7) (R 7) [36,96,10,129,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7589 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7590 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 80, targets := 34 },{ cop := 4, region := 290, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 37 98 14 137 81 288 192 146 274), lower := (rows 37 98 14 137 81 288 192 128 256), losses := [] }

theorem u7590 : Upper (D 7) (R 7) [36,96,10,129,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7590 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7591 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 14 137 146 288 65 208 336), lower := (rows 37 98 14 137 146 288 65 128 256), losses := [] }

theorem u7591 : Upper (D 7) (R 7) [36,96,10,129,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7591 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7592 : PairBound 9 := { available := 65, camps := [], pairs := [(1,0),(2,0)], upper := (rows 37 98 14 137 146 288 80 193 321), lower := (rows 37 98 14 137 146 288 80 128 256), losses := [{ target := 0, region := (rows 0 3 12 8 24 288 92 128 256), good := (rows 102 98 94 222 210 288 80 128 288) }] }

theorem u7592 : Upper (D 7) (R 7) [36,96,10,129,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7592 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7593 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 80, targets := 34 },{ cop := 6, region := 434, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 37 98 14 137 208 288 65 146 274), lower := (rows 37 98 14 137 208 288 65 128 256), losses := [] }

theorem u7593 : Upper (D 7) (R 7) [36,96,10,129,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7593 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7594 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(2,0)], upper := (rows 37 98 14 137 208 288 66 145 273), lower := (rows 37 98 14 137 208 288 66 128 256), losses := [{ target := 0, region := (rows 0 291 12 8 24 288 367 128 256), good := (rows 102 98 94 222 208 354 66 128 354) }] }

theorem u7594 : Upper (D 7) (R 7) [36,96,10,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7594 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7595 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 14 137 208 288 80 131 259), lower := (rows 37 98 14 137 208 288 80 128 256), losses := [] }

theorem u7595 : Upper (D 7) (R 7) [36,96,10,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7595 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7596 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 14 137 400 48 65 194 322), lower := (rows 37 98 14 137 400 48 65 128 256), losses := [] }

theorem u7596 : Upper (D 7) (R 7) [36,96,10,129,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7596 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7597 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(2,0)], upper := (rows 37 98 14 137 400 48 66 193 321), lower := (rows 37 98 14 137 400 48 66 128 256), losses := [{ target := 0, region := (rows 0 51 12 8 16 48 127 128 256), good := (rows 102 98 78 206 498 114 66 128 256) }] }

theorem u7597 : Upper (D 7) (R 7) [36,96,10,129,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7597 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7598 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 37 98 14 152 81 288 65 130 386), lower := (rows 37 98 14 152 81 288 65 128 256), losses := [] }

theorem u7598 : Upper (D 7) (R 7) [36,96,10,144,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7598 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7599 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 2, region := 417, targets := 2 }], pairs := [(0,1),(1,7),(4,7)], upper := (rows 37 98 14 152 81 288 66 129 385), lower := (rows 37 98 14 152 81 288 66 128 256), losses := [] }

theorem u7599 : Upper (D 7) (R 7) [36,96,10,144,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7599 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7600 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 289, targets := 64 },{ cop := 2, region := 289, targets := 128 },{ cop := 4, region := 290, targets := 128 }], pairs := [(0,6),(0,7),(1,7)], upper := (rows 37 98 14 152 81 288 192 131 259), lower := (rows 37 98 14 152 81 288 192 128 256), losses := [] }

theorem u7600 : Upper (D 7) (R 7) [36,96,10,144,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7600 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7601 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 14 152 336 33 65 130 386), lower := (rows 37 98 14 152 336 33 65 128 256), losses := [] }

theorem u7601 : Upper (D 7) (R 7) [36,96,10,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7602 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 152 336 33 66 129 385), lower := (rows 37 98 14 152 336 33 66 128 256), losses := [] }

theorem u7602 : Upper (D 7) (R 7) [36,96,10,144,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7603 : Route 9 := (fun mask => (mask,id))

def c7603 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7603 : Upper (D 7) (R 7) [36,96,10,144,320,1,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,144,320,1,128] 13 (by decide) (choices 1) [1,2] r7603 c7603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u568
  · exact u569

def b7604 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 66, targets := 128 }], pairs := [(0,6),(1,7),(4,6)], upper := (rows 37 98 14 200 146 288 65 145 273), lower := (rows 37 98 14 200 146 288 65 128 256), losses := [] }

theorem u7604 : Upper (D 7) (R 7) [36,96,10,192,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7604 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7605 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 37 98 14 200 146 288 80 129 257), lower := (rows 37 98 14 200 146 288 80 128 256), losses := [] }

theorem u7605 : Upper (D 7) (R 7) [36,96,10,192,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7605 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7606 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 140, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 14 200 273 48 65 130 386), lower := (rows 37 98 14 200 273 48 65 128 256), losses := [] }

theorem u7606 : Upper (D 7) (R 7) [36,96,10,192,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7606 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7607 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 14 200 273 48 66 129 385), lower := (rows 37 98 14 200 273 48 66 128 256), losses := [] }

theorem u7607 : Upper (D 7) (R 7) [36,96,10,192,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7607 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7608 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 14 200 273 48 192 131 259), lower := (rows 37 98 14 200 273 48 192 128 256), losses := [] }

theorem u7608 : Upper (D 7) (R 7) [36,96,10,192,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7608 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7609 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 82, targets := 128 },{ cop := 4, region := 392, targets := 66 }], pairs := [(1,7),(3,1),(3,6),(4,7)], upper := (rows 37 98 14 265 81 160 66 144 400), lower := (rows 37 98 14 265 81 160 66 128 256), losses := [] }

theorem u7609 : Upper (D 7) (R 7) [36,96,10,257,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7610 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 14 265 81 160 80 130 386), lower := (rows 37 98 14 265 81 160 80 128 256), losses := [] }

theorem u7610 : Upper (D 7) (R 7) [36,96,10,257,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7610 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7611 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 14 265 81 160 192 146 274), lower := (rows 37 98 14 265 81 160 192 128 256), losses := [] }

theorem u7611 : Upper (D 7) (R 7) [36,96,10,257,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7612 : PairBound 9 := { available := 80, camps := [{ cop := 5, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(3,5)], upper := (rows 37 98 14 265 145 160 66 208 336), lower := (rows 37 98 14 265 145 160 66 128 256), losses := [{ target := 0, region := (rows 0 179 12 8 16 176 255 144 272), good := (rows 102 98 78 334 498 226 66 226 256) },{ target := 5, region := (rows 1 2 4 25 25 0 70 133 261), good := (rows 477 66 478 409 409 128 66 128 256) }] }

theorem u7612 : Upper (D 7) (R 7) [36,96,10,257,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7613 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 14 265 145 160 80 194 322), lower := (rows 37 98 14 265 145 160 80 128 256), losses := [] }

theorem u7613 : Upper (D 7) (R 7) [36,96,10,257,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7613 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7614 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 178, targets := 1 },{ cop := 0, region := 66, targets := 128 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 37 98 14 265 146 160 65 208 336), lower := (rows 37 98 14 265 146 160 65 128 256), losses := [] }

theorem u7614 : Upper (D 7) (R 7) [36,96,10,257,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7615 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 14 265 146 160 80 193 321), lower := (rows 37 98 14 265 146 160 80 128 256), losses := [] }

theorem u7615 : Upper (D 7) (R 7) [36,96,10,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7615 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7616 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 178, targets := 1 },{ cop := 0, region := 66, targets := 128 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 37 98 14 265 208 160 65 146 274), lower := (rows 37 98 14 265 208 160 65 128 256), losses := [] }

theorem u7616 : Upper (D 7) (R 7) [36,96,10,257,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7617 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 82, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(4,0)], upper := (rows 37 98 14 265 208 160 66 145 273), lower := (rows 37 98 14 265 208 160 66 128 256), losses := [{ target := 0, region := (rows 0 179 12 8 176 176 255 128 256), good := (rows 118 114 78 334 242 242 66 242 256) }] }

theorem u7617 : Upper (D 7) (R 7) [36,96,10,257,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7618 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 14 265 208 160 80 131 259), lower := (rows 37 98 14 265 208 160 80 128 256), losses := [] }

theorem u7618 : Upper (D 7) (R 7) [36,96,10,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7618 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7619 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 430, targets := 1 },{ cop := 6, region := 16, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 37 98 14 280 81 160 65 130 386), lower := (rows 37 98 14 280 81 160 65 128 256), losses := [] }

theorem u7619 : Upper (D 7) (R 7) [36,96,10,272,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7619
end Delivery.IrregularNine14.P07
