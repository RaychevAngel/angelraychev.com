import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0012

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9600 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 37 266 84 137 176 34 65 194 322), lower := (rows 37 266 84 137 176 34 65 128 256), losses := [] }

theorem u9600 : Upper (D 7) (R 7) [36,264,80,129,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9601 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 3, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(2,0),(3,5)], upper := (rows 37 266 84 137 176 34 66 193 321), lower := (rows 37 266 84 137 176 34 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 98 98 128 256), good := (rows 100 362 116 136 244 98 98 128 256) }] }

theorem u9601 : Upper (D 7) (R 7) [36,264,80,129,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9602 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 426, targets := 1 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 266 84 138 19 160 65 224 352), lower := (rows 37 266 84 138 19 160 65 128 256), losses := [] }

theorem u9602 : Upper (D 7) (R 7) [36,264,80,130,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9603 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(2,0),(2,1),(2,7)], upper := (rows 37 266 84 138 19 160 96 193 321), lower := (rows 37 266 84 138 19 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 168 235 128 256), good := (rows 100 362 84 234 86 224 96 224 256) },{ target := 7, region := (rows 1 2 20 8 16 32 97 0 273), good := (rows 357 266 340 10 343 96 96 0 256) }] }

theorem u9603 : Upper (D 7) (R 7) [36,264,80,130,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9604 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 85, targets := 2 },{ cop := 2, region := 426, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(4,1)], upper := (rows 37 266 84 168 145 34 65 194 322), lower := (rows 37 266 84 168 145 34 65 128 256), losses := [] }

theorem u9604 : Upper (D 7) (R 7) [36,264,80,160,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9605 : PairBound 9 := { available := 65, camps := [], pairs := [(0,6),(0,7),(2,5),(4,5)], upper := (rows 37 266 84 168 145 34 66 193 321), lower := (rows 37 266 84 168 145 34 66 128 256), losses := [{ target := 5, region := (rows 1 2 5 8 17 0 98 129 257), good := (rows 469 330 84 200 405 66 66 128 256) },{ target := 6, region := (rows 5 2 4 8 16 98 0 128 256), good := (rows 37 298 53 168 145 34 34 128 256) },{ target := 7, region := (rows 5 2 4 8 16 98 98 0 261), good := (rows 357 362 373 104 273 98 98 0 256) }] }

theorem u9605 : Upper (D 7) (R 7) [36,264,80,160,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9606 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 68, targets := 162 },{ cop := 2, region := 426, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(2,7)], upper := (rows 37 266 84 200 19 160 65 162 290), lower := (rows 37 266 84 200 19 160 65 128 256), losses := [] }

theorem u9606 : Upper (D 7) (R 7) [36,264,80,192,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9607 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 68, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 84 200 19 160 66 161 289), lower := (rows 37 266 84 200 19 160 66 128 256), losses := [] }

theorem u9607 : Upper (D 7) (R 7) [36,264,80,192,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9608 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 72, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 37 266 84 200 19 160 96 131 259), lower := (rows 37 266 84 200 19 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 168 16 168 235 128 256), good := (rows 108 362 84 232 86 232 104 232 256) },{ target := 1, region := (rows 1 0 20 168 16 168 235 128 256), good := (rows 109 360 84 232 85 232 104 232 256) }] }

theorem u9608 : Upper (D 7) (R 7) [36,264,80,192,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9609 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 266 84 200 145 34 65 162 290), lower := (rows 37 266 84 200 145 34 65 128 256), losses := [] }

theorem u9609 : Upper (D 7) (R 7) [36,264,80,192,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9610 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 144, targets := 66 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 37 266 84 200 145 34 66 161 289), lower := (rows 37 266 84 200 145 34 66 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 21 98 0 133 261), good := (rows 437 298 437 168 401 34 34 128 256) },{ target := 7, region := (rows 5 2 4 8 16 98 98 0 261), good := (rows 357 362 373 104 273 98 98 0 256) }] }

theorem u9610 : Upper (D 7) (R 7) [36,264,80,192,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9611 : PairBound 9 := { available := 3, camps := [], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 37 266 84 200 145 34 96 131 259), lower := (rows 37 266 84 200 145 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 34 99 128 256), good := (rows 100 362 92 200 220 98 96 128 256) },{ target := 1, region := (rows 1 0 20 24 16 32 97 128 256), good := (rows 101 264 92 200 221 96 96 128 256) }] }

theorem u9611 : Upper (D 7) (R 7) [36,264,80,192,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9611 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9612 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 37 266 84 200 176 34 65 131 259), lower := (rows 37 266 84 200 176 34 65 128 256), losses := [] }

theorem u9612 : Upper (D 7) (R 7) [36,264,80,192,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9613 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(3,5),(4,1),(4,6)], upper := (rows 37 266 84 200 176 34 66 129 257), lower := (rows 37 266 84 200 176 34 66 128 256), losses := [] }

theorem u9613 : Upper (D 7) (R 7) [36,264,80,192,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9614 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 213, targets := 2 },{ cop := 4, region := 132, targets := 1 }], pairs := [(0,1),(2,0),(2,1),(4,1)], upper := (rows 37 266 196 11 112 34 65 144 400), lower := (rows 37 266 196 11 112 34 65 128 256), losses := [] }

theorem u9614 : Upper (D 7) (R 7) [36,264,192,3,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9615 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 299, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 266 196 11 112 34 80 129 385), lower := (rows 37 266 196 11 112 34 80 128 256), losses := [] }

theorem u9615 : Upper (D 7) (R 7) [36,264,192,3,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9615 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9616 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 11 112 34 192 145 273), lower := (rows 37 266 196 11 112 34 192 128 256), losses := [] }

theorem u9616 : Upper (D 7) (R 7) [36,264,192,3,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9617 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 418, targets := 65 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(1,0),(1,6),(2,1)], upper := (rows 37 266 196 25 82 34 65 160 416), lower := (rows 37 266 196 25 82 34 65 128 256), losses := [] }

theorem u9617 : Upper (D 7) (R 7) [36,264,192,17,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9618 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 112, targets := 129 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,7)], upper := (rows 37 266 196 25 82 34 96 129 385), lower := (rows 37 266 196 25 82 34 96 128 256), losses := [] }

theorem u9618 : Upper (D 7) (R 7) [36,264,192,17,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9619 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 25 82 34 192 161 289), lower := (rows 37 266 196 25 82 34 192 128 256), losses := [] }

theorem u9619 : Upper (D 7) (R 7) [36,264,192,17,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9620 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 266 196 25 112 34 65 130 386), lower := (rows 37 266 196 25 112 34 65 128 256), losses := [] }

theorem u9620 : Upper (D 7) (R 7) [36,264,192,17,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9621 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 141, targets := 2 },{ cop := 1, region := 112, targets := 1 }], pairs := [(0,1),(2,1),(3,1),(4,0)], upper := (rows 37 266 196 25 112 34 66 129 385), lower := (rows 37 266 196 25 112 34 66 128 256), losses := [] }

theorem u9621 : Upper (D 7) (R 7) [36,264,192,17,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9622 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 25 112 34 192 131 259), lower := (rows 37 266 196 25 112 34 192 128 256), losses := [] }

theorem u9622 : Upper (D 7) (R 7) [36,264,192,17,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9623 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 266 196 56 81 34 65 130 386), lower := (rows 37 266 196 56 81 34 65 128 256), losses := [] }

theorem u9623 : Upper (D 7) (R 7) [36,264,192,48,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9624 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 132, targets := 34 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6),(2,1),(2,5),(3,6)], upper := (rows 37 266 196 56 81 34 66 129 385), lower := (rows 37 266 196 56 81 34 66 128 256), losses := [] }

theorem u9624 : Upper (D 7) (R 7) [36,264,192,48,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9625 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 56 81 34 192 131 259), lower := (rows 37 266 196 56 81 34 192 128 256), losses := [] }

theorem u9625 : Upper (D 7) (R 7) [36,264,192,48,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9626 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 386, targets := 97 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,0),(1,5),(1,6)], upper := (rows 37 266 196 56 82 33 65 130 386), lower := (rows 37 266 196 56 82 33 65 128 256), losses := [] }

theorem u9626 : Upper (D 7) (R 7) [36,264,192,48,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9627 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 80, targets := 161 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 37 266 196 56 82 33 66 129 385), lower := (rows 37 266 196 56 82 33 66 128 256), losses := [] }

theorem u9627 : Upper (D 7) (R 7) [36,264,192,48,66,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9628 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 56 82 33 192 131 259), lower := (rows 37 266 196 56 82 33 192 128 256), losses := [] }

theorem u9628 : Upper (D 7) (R 7) [36,264,192,48,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9629 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 37 266 196 73 19 34 80 160 416), lower := (rows 37 266 196 73 19 34 80 128 256), losses := [] }

theorem u9629 : Upper (D 7) (R 7) [36,264,192,65,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9629 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9630 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 266 196 73 19 34 96 144 400), lower := (rows 37 266 196 73 19 34 96 128 256), losses := [] }

theorem u9630 : Upper (D 7) (R 7) [36,264,192,65,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9631 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 73 19 34 192 176 304), lower := (rows 37 266 196 73 19 34 192 128 256), losses := [] }

theorem u9631 : Upper (D 7) (R 7) [36,264,192,65,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9632 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 266 196 73 146 34 65 176 304), lower := (rows 37 266 196 73 146 34 65 128 256), losses := [] }

theorem u9632 : Upper (D 7) (R 7) [36,264,192,65,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9633 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 266 196 73 146 34 80 161 289), lower := (rows 37 266 196 73 146 34 80 128 256), losses := [] }

theorem u9633 : Upper (D 7) (R 7) [36,264,192,65,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9633 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9634 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 266 196 73 146 34 96 145 273), lower := (rows 37 266 196 73 146 34 96 128 256), losses := [] }

theorem u9634 : Upper (D 7) (R 7) [36,264,192,65,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9635 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 266 196 73 176 34 65 146 274), lower := (rows 37 266 196 73 176 34 65 128 256), losses := [] }

theorem u9635 : Upper (D 7) (R 7) [36,264,192,65,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9636 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,0),(4,1),(4,6)], upper := (rows 37 266 196 73 176 34 66 145 273), lower := (rows 37 266 196 73 176 34 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 20 98 98 128 256), good := (rows 116 362 244 104 244 98 98 128 256) }] }

theorem u9636 : Upper (D 7) (R 7) [36,264,192,65,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9637 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 266 196 73 176 34 80 131 259), lower := (rows 37 266 196 73 176 34 80 128 256), losses := [] }

theorem u9637 : Upper (D 7) (R 7) [36,264,192,65,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9637 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9638 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 4, region := 72, targets := 32 }], pairs := [(0,1),(2,1),(3,5)], upper := (rows 37 266 196 74 19 48 65 160 416), lower := (rows 37 266 196 74 19 48 65 128 256), losses := [] }

theorem u9638 : Upper (D 7) (R 7) [36,264,192,66,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9638 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9639 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 104, targets := 129 },{ cop := 4, region := 229, targets := 2 }], pairs := [(0,1),(3,0),(3,7)], upper := (rows 37 266 196 74 19 48 96 129 385), lower := (rows 37 266 196 74 19 48 96 128 256), losses := [] }

theorem u9639 : Upper (D 7) (R 7) [36,264,192,66,3,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9639 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9640 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 266 196 74 19 48 192 161 289), lower := (rows 37 266 196 74 19 48 192 128 256), losses := [] }

theorem u9640 : Upper (D 7) (R 7) [36,264,192,66,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9640 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9641 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 266 196 88 50 33 65 130 386), lower := (rows 37 266 196 88 50 33 65 128 256), losses := [] }

theorem u9641 : Upper (D 7) (R 7) [36,264,192,80,34,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9642 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 72, targets := 161 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,7)], upper := (rows 37 266 196 88 50 33 66 129 385), lower := (rows 37 266 196 88 50 33 66 128 256), losses := [] }

theorem u9642 : Upper (D 7) (R 7) [36,264,192,80,34,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9643 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 88 50 33 192 131 259), lower := (rows 37 266 196 88 50 33 192 128 256), losses := [] }

theorem u9643 : Upper (D 7) (R 7) [36,264,192,80,34,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9644 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 266 196 88 145 34 65 162 290), lower := (rows 37 266 196 88 145 34 65 128 256), losses := [] }

theorem u9644 : Upper (D 7) (R 7) [36,264,192,80,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9645 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 37 266 196 88 145 34 66 161 289), lower := (rows 37 266 196 88 145 34 66 128 256), losses := [] }

theorem u9645 : Upper (D 7) (R 7) [36,264,192,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9646 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,0),(3,0),(3,7)], upper := (rows 37 266 196 88 145 34 96 131 259), lower := (rows 37 266 196 88 145 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 34 99 128 256), good := (rows 100 362 196 92 220 98 96 128 256) }] }

theorem u9646 : Upper (D 7) (R 7) [36,264,192,80,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9647 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 109, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 37 266 196 88 146 33 65 162 290), lower := (rows 37 266 196 88 146 33 65 128 256), losses := [] }

theorem u9647 : Upper (D 7) (R 7) [36,264,192,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9648 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 266 196 88 146 33 66 161 289), lower := (rows 37 266 196 88 146 33 66 128 256), losses := [] }

theorem u9648 : Upper (D 7) (R 7) [36,264,192,80,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9649 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 37 266 196 88 146 33 96 131 259), lower := (rows 37 266 196 88 146 33 96 128 256), losses := [] }

theorem u9649 : Upper (D 7) (R 7) [36,264,192,80,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9650 : Route 9 := (fun mask => (mask,id))

def c9650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9650 : Upper (D 7) (R 7) [36,264,192,80,130,2,1] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80,130,2,1] 13 (by decide) (choices 1) [1,32] r9650 c9650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u755
  · exact u756

def b9651 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 108, targets := 1 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(2,0),(2,1),(3,0)], upper := (rows 37 266 196 88 146 34 96 129 257), lower := (rows 37 266 196 88 146 34 96 128 256), losses := [] }

theorem u9651 : Upper (D 7) (R 7) [36,264,192,80,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9652 : Route 9 := (fun mask => (mask,id))

def c9652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u9652 : Upper (D 7) (R 7) [36,264,192,80,160,2,1] 13 := by
  apply FastRouting.sound _ _ [36,264,192,80,160,2,1] 13 (by decide) (choices 1) [1,2] r9652 c9652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u757
  · exact u758

def b9653 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 144, targets := 66 }], pairs := [(2,0),(3,0),(4,1),(4,6)], upper := (rows 37 266 196 88 176 34 66 129 257), lower := (rows 37 266 196 88 176 34 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 29 20 98 98 128 256), good := (rows 124 362 252 124 252 98 98 128 256) }] }

theorem u9653 : Upper (D 7) (R 7) [36,264,192,80,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9654 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 130 },{ cop := 4, region := 196, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,7)], upper := (rows 37 266 196 104 19 34 65 144 400), lower := (rows 37 266 196 104 19 34 65 128 256), losses := [] }

theorem u9654 : Upper (D 7) (R 7) [36,264,192,96,3,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9655 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 133, targets := 2 },{ cop := 4, region := 104, targets := 1 }], pairs := [(0,1),(2,1),(3,0)], upper := (rows 37 266 196 104 19 34 80 129 385), lower := (rows 37 266 196 104 19 34 80 128 256), losses := [] }

theorem u9655 : Upper (D 7) (R 7) [36,264,192,96,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9655 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9656 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 266 196 104 19 34 192 145 273), lower := (rows 37 266 196 104 19 34 192 128 256), losses := [] }

theorem u9656 : Upper (D 7) (R 7) [36,264,192,96,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9657 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 266 196 104 19 48 65 130 386), lower := (rows 37 266 196 104 19 48 65 128 256), losses := [] }

theorem u9657 : Upper (D 7) (R 7) [36,264,192,96,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9657 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9658 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 133, targets := 2 },{ cop := 4, region := 104, targets := 1 }], pairs := [(0,1),(2,1),(3,0)], upper := (rows 37 266 196 104 19 48 66 129 385), lower := (rows 37 266 196 104 19 48 66 128 256), losses := [] }

theorem u9658 : Upper (D 7) (R 7) [36,264,192,96,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9658 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9659 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 266 196 104 19 48 192 131 259), lower := (rows 37 266 196 104 19 48 192 128 256), losses := [] }

theorem u9659 : Upper (D 7) (R 7) [36,264,192,96,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9659 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9659
end Delivery.IrregularNine14.P07
