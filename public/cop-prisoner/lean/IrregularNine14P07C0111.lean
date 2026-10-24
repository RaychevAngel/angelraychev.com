import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6660 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 74, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 37 42 21 74 336 160 65 130 386), lower := (rows 37 42 21 74 336 160 65 128 256), losses := [] }

theorem u6660 : Upper (D 7) (R 7) [36,40,17,66,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6661 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 42 21 74 336 160 66 129 385), lower := (rows 37 42 21 74 336 160 66 128 256), losses := [] }

theorem u6661 : Upper (D 7) (R 7) [36,40,17,66,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6662 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 74, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 42 21 74 336 160 192 131 259), lower := (rows 37 42 21 74 336 160 192 128 256), losses := [{ target := 1, region := (rows 17 0 20 8 16 224 224 128 256), good := (rows 101 104 21 104 373 224 224 224 256) }] }

theorem u6662 : Upper (D 7) (R 7) [36,40,17,66,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6663 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 42 21 200 82 288 65 130 386), lower := (rows 37 42 21 200 82 288 65 128 256), losses := [] }

theorem u6663 : Upper (D 7) (R 7) [36,40,17,192,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6663 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6664 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 42 21 200 82 288 66 129 385), lower := (rows 37 42 21 200 82 288 66 128 256), losses := [] }

theorem u6664 : Upper (D 7) (R 7) [36,40,17,192,66,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6664 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6665 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 42 21 200 82 288 192 131 259), lower := (rows 37 42 21 200 82 288 192 128 256), losses := [] }

theorem u6665 : Upper (D 7) (R 7) [36,40,17,192,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6665 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6666 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 37 42 21 200 336 34 65 130 386), lower := (rows 37 42 21 200 336 34 65 128 256), losses := [] }

theorem u6666 : Upper (D 7) (R 7) [36,40,17,192,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6667 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 3, region := 34, targets := 64 },{ cop := 7, region := 106, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 42 21 200 336 34 66 129 385), lower := (rows 37 42 21 200 336 34 66 128 256), losses := [] }

theorem u6667 : Upper (D 7) (R 7) [36,40,17,192,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6668 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 42 21 200 336 34 192 131 259), lower := (rows 37 42 21 200 336 34 192 128 256), losses := [] }

theorem u6668 : Upper (D 7) (R 7) [36,40,17,192,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6669 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 6, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 21 266 82 160 65 192 448), lower := (rows 37 42 21 266 82 160 65 128 256), losses := [] }

theorem u6669 : Upper (D 7) (R 7) [36,40,17,258,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6670 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,5)], upper := (rows 37 42 21 266 82 160 192 193 321), lower := (rows 37 42 21 266 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 224 224 128 256), good := (rows 100 122 20 282 114 224 224 224 256) },{ target := 5, region := (rows 1 2 4 8 18 0 229 133 261), good := (rows 453 90 469 282 82 192 192 192 256) }] }

theorem u6670 : Upper (D 7) (R 7) [36,40,17,258,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6671 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 6, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 21 328 82 160 65 130 386), lower := (rows 37 42 21 328 82 160 65 128 256), losses := [] }

theorem u6671 : Upper (D 7) (R 7) [36,40,17,320,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6672 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 4, region := 165, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 42 21 328 82 160 66 129 385), lower := (rows 37 42 21 328 82 160 66 128 256), losses := [] }

theorem u6672 : Upper (D 7) (R 7) [36,40,17,320,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6673 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 42 21 328 82 160 192 131 259), lower := (rows 37 42 21 328 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 26 224 224 128 256), good := (rows 100 122 20 378 114 224 224 224 256) }] }

theorem u6673 : Upper (D 7) (R 7) [36,40,17,320,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6674 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 37 42 21 328 208 34 65 130 386), lower := (rows 37 42 21 328 208 34 65 128 256), losses := [] }

theorem u6674 : Upper (D 7) (R 7) [36,40,17,320,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6675 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 106, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 42 21 328 208 34 66 129 385), lower := (rows 37 42 21 328 208 34 66 128 256), losses := [] }

theorem u6675 : Upper (D 7) (R 7) [36,40,17,320,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6676 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 42 21 328 208 34 192 131 259), lower := (rows 37 42 21 328 208 34 192 128 256), losses := [] }

theorem u6676 : Upper (D 7) (R 7) [36,40,17,320,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6677 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 42 22 73 208 288 65 130 386), lower := (rows 37 42 22 73 208 288 65 128 256), losses := [] }

theorem u6677 : Upper (D 7) (R 7) [36,40,18,65,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6677 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6678 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 2, region := 417, targets := 2 }], pairs := [(0,1),(1,7),(3,7)], upper := (rows 37 42 22 73 208 288 66 129 385), lower := (rows 37 42 22 73 208 288 66 128 256), losses := [] }

theorem u6678 : Upper (D 7) (R 7) [36,40,18,65,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6678 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6679 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 42 22 73 208 288 192 131 259), lower := (rows 37 42 22 73 208 288 192 128 256), losses := [] }

theorem u6679 : Upper (D 7) (R 7) [36,40,18,65,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6679 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6680 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 162, targets := 1 },{ cop := 3, region := 400, targets := 2 }], pairs := [(1,0),(1,7),(3,7),(4,1)], upper := (rows 37 42 22 73 273 160 66 192 448), lower := (rows 37 42 22 73 273 160 66 128 256), losses := [] }

theorem u6680 : Upper (D 7) (R 7) [36,40,18,65,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6681 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(4,5)], upper := (rows 37 42 22 73 273 160 192 194 322), lower := (rows 37 42 22 73 273 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 224 224 128 256), good := (rows 109 104 20 105 281 224 224 224 256) },{ target := 5, region := (rows 1 2 4 25 17 0 231 134 262), good := (rows 477 458 478 89 345 192 192 192 256) }] }

theorem u6681 : Upper (D 7) (R 7) [36,40,18,65,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6682 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 438, targets := 1 },{ cop := 6, region := 8, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 37 42 22 73 336 160 65 130 386), lower := (rows 37 42 22 73 336 160 65 128 256), losses := [] }

theorem u6682 : Upper (D 7) (R 7) [36,40,18,65,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6683 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 2, region := 161, targets := 66 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 42 22 73 336 160 66 129 385), lower := (rows 37 42 22 73 336 160 66 128 256), losses := [] }

theorem u6683 : Upper (D 7) (R 7) [36,40,18,65,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6684 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 161, targets := 64 },{ cop := 3, region := 162, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(3,1)], upper := (rows 37 42 22 73 336 160 192 131 259), lower := (rows 37 42 22 73 336 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 224 224 128 256), good := (rows 100 106 22 106 368 224 224 224 256) },{ target := 1, region := (rows 1 0 4 9 16 224 224 128 256), good := (rows 109 104 20 105 368 224 224 224 256) }] }

theorem u6684 : Upper (D 7) (R 7) [36,40,18,65,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6685 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 37 42 22 200 81 288 65 130 386), lower := (rows 37 42 22 200 81 288 65 128 256), losses := [] }

theorem u6685 : Upper (D 7) (R 7) [36,40,18,192,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6685 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6686 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 42 22 200 81 288 66 129 385), lower := (rows 37 42 22 200 81 288 66 128 256), losses := [] }

theorem u6686 : Upper (D 7) (R 7) [36,40,18,192,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6686 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6687 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 42 22 200 81 288 192 131 259), lower := (rows 37 42 22 200 81 288 192 128 256), losses := [] }

theorem u6687 : Upper (D 7) (R 7) [36,40,18,192,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6687 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6688 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 42 22 200 336 33 65 130 386), lower := (rows 37 42 22 200 336 33 65 128 256), losses := [{ target := 5, region := (rows 1 2 6 11 19 0 97 134 262), good := (rows 477 478 414 200 336 89 89 128 256) }] }

theorem u6688 : Upper (D 7) (R 7) [36,40,18,192,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6689 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 42 22 200 336 33 66 129 385), lower := (rows 37 42 22 200 336 33 66 128 256), losses := [{ target := 5, region := (rows 1 2 70 11 19 0 70 161 289), good := (rows 477 478 94 204 340 409 94 128 256) }] }

theorem u6689 : Upper (D 7) (R 7) [36,40,18,192,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6690 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 42 22 200 336 33 192 131 259), lower := (rows 37 42 22 200 336 33 192 128 256), losses := [] }

theorem u6690 : Upper (D 7) (R 7) [36,40,18,192,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6691 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 22 265 81 160 66 192 448), lower := (rows 37 42 22 265 81 160 66 128 256), losses := [] }

theorem u6691 : Upper (D 7) (R 7) [36,40,18,257,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6692 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(2,5),(3,5),(4,1)], upper := (rows 37 42 22 265 81 160 192 194 322), lower := (rows 37 42 22 265 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 224 224 128 256), good := (rows 117 104 20 281 113 224 224 224 256) },{ target := 5, region := (rows 1 2 6 9 25 0 231 134 262), good := (rows 477 478 470 345 89 192 192 192 256) }] }

theorem u6692 : Upper (D 7) (R 7) [36,40,18,257,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6693 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 37 42 22 328 81 160 65 130 386), lower := (rows 37 42 22 328 81 160 65 128 256), losses := [] }

theorem u6693 : Upper (D 7) (R 7) [36,40,18,320,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6694 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 42 22 328 81 160 66 129 385), lower := (rows 37 42 22 328 81 160 66 128 256), losses := [] }

theorem u6694 : Upper (D 7) (R 7) [36,40,18,320,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6694 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6695 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(1,0),(4,1),(4,5)], upper := (rows 37 42 22 328 81 160 192 131 259), lower := (rows 37 42 22 328 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 224 224 128 256), good := (rows 100 106 22 362 112 224 224 224 256) },{ target := 1, region := (rows 1 0 4 8 17 224 224 128 256), good := (rows 117 104 20 360 113 224 224 224 256) },{ target := 5, region := (rows 1 2 4 8 17 0 224 128 256), good := (rows 85 74 22 328 81 192 192 192 256) }] }

theorem u6695 : Upper (D 7) (R 7) [36,40,18,320,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6695 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6696 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 42 22 328 208 33 65 130 386), lower := (rows 37 42 22 328 208 33 65 128 256), losses := [{ target := 5, region := (rows 1 2 6 11 19 0 97 134 262), good := (rows 477 478 414 328 208 89 89 128 256) }] }

theorem u6696 : Upper (D 7) (R 7) [36,40,18,320,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6696 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6697 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 42 22 328 208 33 66 129 385), lower := (rows 37 42 22 328 208 33 66 128 256), losses := [{ target := 5, region := (rows 1 2 70 11 19 0 70 161 289), good := (rows 477 478 94 332 212 409 94 128 256) }] }

theorem u6697 : Upper (D 7) (R 7) [36,40,18,320,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6698 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 42 22 328 208 33 192 131 259), lower := (rows 37 42 22 328 208 33 192 128 256), losses := [] }

theorem u6698 : Upper (D 7) (R 7) [36,40,18,320,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6699 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 37 42 69 88 146 288 65 130 386), lower := (rows 37 42 69 88 146 288 65 128 256), losses := [] }

theorem u6699 : Upper (D 7) (R 7) [36,40,65,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6699 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6700 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 72, targets := 161 }], pairs := [(3,0),(3,5),(3,7)], upper := (rows 37 42 69 88 146 288 66 129 385), lower := (rows 37 42 69 88 146 288 66 128 256), losses := [] }

theorem u6700 : Upper (D 7) (R 7) [36,40,65,80,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6700 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6701 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 42 69 88 146 288 192 131 259), lower := (rows 37 42 69 88 146 288 192 128 256), losses := [] }

theorem u6701 : Upper (D 7) (R 7) [36,40,65,80,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6701 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6702 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 42 69 88 273 160 66 130 386), lower := (rows 37 42 69 88 273 160 66 128 256), losses := [] }

theorem u6702 : Upper (D 7) (R 7) [36,40,65,80,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6703 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 42 69 88 273 160 192 130 258), lower := (rows 37 42 69 88 273 160 192 128 256), losses := [] }

theorem u6703 : Upper (D 7) (R 7) [36,40,65,80,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6704 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 42 69 88 274 160 65 130 386), lower := (rows 37 42 69 88 274 160 65 128 256), losses := [] }

theorem u6704 : Upper (D 7) (R 7) [36,40,65,80,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6705 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 72, targets := 161 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,7)], upper := (rows 37 42 69 88 274 160 66 129 385), lower := (rows 37 42 69 88 274 160 66 128 256), losses := [] }

theorem u6705 : Upper (D 7) (R 7) [36,40,65,80,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6706 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 2 }], pairs := [(0,1),(1,0),(2,1),(2,5)], upper := (rows 37 42 69 88 274 160 192 131 259), lower := (rows 37 42 69 88 274 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 224 224 128 256), good := (rows 100 106 100 122 274 224 224 224 256) },{ target := 5, region := (rows 1 2 5 8 16 0 224 128 256), good := (rows 69 74 69 88 274 192 192 192 256) }] }

theorem u6706 : Upper (D 7) (R 7) [36,40,65,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6707 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 426, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 37 42 69 138 82 288 65 144 400), lower := (rows 37 42 69 138 82 288 65 128 256), losses := [] }

theorem u6707 : Upper (D 7) (R 7) [36,40,65,130,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6707 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6708 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 42 69 138 82 288 80 129 385), lower := (rows 37 42 69 138 82 288 80 128 256), losses := [] }

theorem u6708 : Upper (D 7) (R 7) [36,40,65,130,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6708 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6709 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 80, targets := 33 },{ cop := 4, region := 293, targets := 2 }], pairs := [(0,1),(4,0),(4,5)], upper := (rows 37 42 69 138 82 288 192 145 273), lower := (rows 37 42 69 138 82 288 192 128 256), losses := [] }

theorem u6709 : Upper (D 7) (R 7) [36,40,65,130,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6709 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6710 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 37 42 69 138 208 288 65 146 274), lower := (rows 37 42 69 138 208 288 65 128 256), losses := [] }

theorem u6710 : Upper (D 7) (R 7) [36,40,65,130,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6710 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6711 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 437, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 42 69 138 208 288 66 145 273), lower := (rows 37 42 69 138 208 288 66 128 256), losses := [] }

theorem u6711 : Upper (D 7) (R 7) [36,40,65,130,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6711 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6712 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 37 42 69 138 208 288 80 131 259), lower := (rows 37 42 69 138 208 288 80 128 256), losses := [] }

theorem u6712 : Upper (D 7) (R 7) [36,40,65,130,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6712 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6713 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 426, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 37 42 69 152 82 288 65 130 386), lower := (rows 37 42 69 152 82 288 65 128 256), losses := [] }

theorem u6713 : Upper (D 7) (R 7) [36,40,65,144,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6713 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6714 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 42 69 152 82 288 66 129 385), lower := (rows 37 42 69 152 82 288 66 128 256), losses := [] }

theorem u6714 : Upper (D 7) (R 7) [36,40,65,144,66,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6714 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6715 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 293, targets := 128 }], pairs := [(0,7),(2,7),(4,0)], upper := (rows 37 42 69 152 82 288 192 131 259), lower := (rows 37 42 69 152 82 288 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 288 200 128 256), good := (rows 36 122 68 216 82 288 192 192 288) }] }

theorem u6715 : Upper (D 7) (R 7) [36,40,65,144,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6715 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6716 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 170, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 42 69 152 336 34 65 130 386), lower := (rows 37 42 69 152 336 34 65 128 256), losses := [] }

theorem u6716 : Upper (D 7) (R 7) [36,40,65,144,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6717 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 69 152 336 34 66 129 385), lower := (rows 37 42 69 152 336 34 66 128 256), losses := [] }

theorem u6717 : Upper (D 7) (R 7) [36,40,65,144,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6718 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 34, targets := 192 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,6),(1,7)], upper := (rows 37 42 69 152 336 34 192 131 259), lower := (rows 37 42 69 152 336 34 192 128 256), losses := [{ target := 1, region := (rows 35 0 6 8 16 32 200 128 256), good := (rows 37 109 69 216 336 37 192 192 256) }] }

theorem u6718 : Upper (D 7) (R 7) [36,40,65,144,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6718 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6719 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 42 69 200 145 288 66 146 274), lower := (rows 37 42 69 200 145 288 66 128 256), losses := [] }

theorem u6719 : Upper (D 7) (R 7) [36,40,65,192,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6719 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u6719
end Delivery.IrregularNine14.P07
