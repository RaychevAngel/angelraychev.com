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

def b600 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 229, targets := 2 },{ cop := 4, region := 264, targets := 65 }], pairs := [(0,1),(2,1),(3,0),(3,6)], upper := (rows 37 98 76 280 146 160 65 129 258), lower := (rows 37 98 76 280 146 160 65 129 256), losses := [] }

theorem u600 : Upper (D 7) (R 7) [36,96,72,272,130,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b601 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 365, targets := 2 },{ cop := 1, region := 144, targets := 1 }], pairs := [(0,1),(2,1),(3,1),(4,0)], upper := (rows 37 98 76 280 146 160 65 130 257), lower := (rows 37 98 76 280 146 160 65 130 256), losses := [] }

theorem u601 : Upper (D 7) (R 7) [36,96,72,272,130,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b602 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 177, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 76 392 145 48 66 129 258), lower := (rows 37 98 76 392 145 48 66 129 256), losses := [] }

theorem u602 : Upper (D 7) (R 7) [36,96,72,384,129,16,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b602 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b603 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 264, targets := 66 },{ cop := 0, region := 66, targets := 1 }], pairs := [(1,0),(3,1),(3,6)], upper := (rows 37 98 76 392 145 48 66 130 257), lower := (rows 37 98 76 392 145 48 66 130 256), losses := [] }

theorem u603 : Upper (D 7) (R 7) [36,96,72,384,129,16,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b603 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b604 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 264, targets := 65 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7),(3,0),(3,6)], upper := (rows 37 98 76 392 146 48 65 129 258), lower := (rows 37 98 76 392 146 48 65 129 256), losses := [] }

theorem u604 : Upper (D 7) (R 7) [36,96,72,384,130,16,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b604 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b605 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 365, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 76 392 146 48 65 130 257), lower := (rows 37 98 76 392 146 48 65 130 256), losses := [] }

theorem u605 : Upper (D 7) (R 7) [36,96,72,384,130,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b605 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b606 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 133 25 336 34 192 130 264), lower := (rows 37 98 133 25 336 34 192 130 256), losses := [] }

theorem u606 : Upper (D 7) (R 7) [36,96,129,17,320,2,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b606 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b607 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 306, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 133 25 336 34 192 136 258), lower := (rows 37 98 133 25 336 34 192 136 256), losses := [] }

theorem u607 : Upper (D 7) (R 7) [36,96,129,17,320,2,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b607 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b608 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 336, targets := 34 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(4,1),(4,5)], upper := (rows 37 98 133 26 273 34 192 136 320), lower := (rows 37 98 133 26 273 34 192 136 256), losses := [] }

theorem u608 : Upper (D 7) (R 7) [36,96,129,18,257,2,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b608 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b609 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(3,0)], upper := (rows 37 98 133 26 273 34 192 192 264), lower := (rows 37 98 133 26 273 34 192 192 256), losses := [] }

theorem u609 : Upper (D 7) (R 7) [36,96,129,18,257,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b610 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 2, region := 336, targets := 2 }], pairs := [(0,6),(2,6),(4,1)], upper := (rows 37 98 133 26 273 40 192 130 320), lower := (rows 37 98 133 26 273 40 192 130 256), losses := [] }

theorem u610 : Upper (D 7) (R 7) [36,96,129,18,257,8,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b610 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b611 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 37 98 133 26 273 40 192 192 258), lower := (rows 37 98 133 26 273 40 192 192 256), losses := [] }

theorem u611 : Upper (D 7) (R 7) [36,96,129,18,257,8,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b611 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b612 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 344, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 133 88 273 34 192 130 264), lower := (rows 37 98 133 88 273 34 192 130 256), losses := [] }

theorem u612 : Upper (D 7) (R 7) [36,96,129,80,257,2,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b613 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 204, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 37 98 133 88 273 34 192 136 258), lower := (rows 37 98 133 88 273 34 192 136 256), losses := [] }

theorem u613 : Upper (D 7) (R 7) [36,96,129,80,257,2,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b613 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b614 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 148, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 134 25 208 288 65 130 264), lower := (rows 37 98 134 25 208 288 65 130 256), losses := [] }

theorem u614 : Upper (D 7) (R 7) [36,96,130,17,192,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b614 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b615 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 37 98 134 25 208 288 65 136 258), lower := (rows 37 98 134 25 208 288 65 136 256), losses := [] }

theorem u615 : Upper (D 7) (R 7) [36,96,130,17,192,256,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b615 [(5,8),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b616 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 272, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 37 98 134 25 274 40 192 129 320), lower := (rows 37 98 134 25 274 40 192 129 256), losses := [] }

theorem u616 : Upper (D 7) (R 7) [36,96,130,17,258,8,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b616 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b617 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 313, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 98 134 25 274 40 192 192 257), lower := (rows 37 98 134 25 274 40 192 192 256), losses := [] }

theorem u617 : Upper (D 7) (R 7) [36,96,130,17,258,8,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b617 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b618 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 306, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 37 98 140 25 336 34 192 129 258), lower := (rows 37 98 140 25 336 34 192 129 256), losses := [] }

theorem u618 : Upper (D 7) (R 7) [36,96,136,17,320,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b619 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 230, targets := 1 },{ cop := 4, region := 34, targets := 128 },{ cop := 8, region := 242, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(4,0)], upper := (rows 37 98 140 25 336 34 192 130 257), lower := (rows 37 98 140 25 336 34 192 130 256), losses := [] }

theorem u619 : Upper (D 7) (R 7) [36,96,136,17,320,2,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b620 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 290, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 140 88 146 288 65 129 258), lower := (rows 37 98 140 88 146 288 65 129 256), losses := [] }

theorem u620 : Upper (D 7) (R 7) [36,96,136,80,130,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b620 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b621 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 156, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 140 88 146 288 65 130 257), lower := (rows 37 98 140 88 146 288 65 130 256), losses := [] }

theorem u621 : Upper (D 7) (R 7) [36,96,136,80,130,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b621 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b622 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 140 88 400 34 65 129 258), lower := (rows 37 98 140 88 400 34 65 129 256), losses := [{ target := 0, region := (rows 0 74 4 8 20 110 64 128 366), good := (rows 308 354 446 378 400 290 354 128 256) }] }

theorem u622 : Upper (D 7) (R 7) [36,96,136,80,384,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b623 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 166, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 98 140 88 400 34 65 130 257), lower := (rows 37 98 140 88 400 34 65 130 256), losses := [] }

theorem u623 : Upper (D 7) (R 7) [36,96,136,80,384,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b624 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 264, targets := 161 }], pairs := [(3,0),(3,5),(3,7)], upper := (rows 37 98 140 328 146 48 65 129 258), lower := (rows 37 98 140 328 146 48 65 129 256), losses := [] }

theorem u624 : Upper (D 7) (R 7) [36,96,136,320,130,16,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b624 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b625 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 182, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 140 328 146 48 65 130 257), lower := (rows 37 98 140 328 146 48 65 130 256), losses := [] }

theorem u625 : Upper (D 7) (R 7) [36,96,136,320,130,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b625 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b626 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 133, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 37 98 196 25 146 40 320 129 258), lower := (rows 37 98 196 25 146 40 320 129 256), losses := [] }

theorem u626 : Upper (D 7) (R 7) [36,96,192,17,130,8,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b626 [(5,3),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b627 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 132, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 37 98 196 25 146 40 320 130 257), lower := (rows 37 98 196 25 146 40 320 130 256), losses := [] }

theorem u627 : Upper (D 7) (R 7) [36,96,192,17,130,8,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b627 [(5,3),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b628 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 148, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 196 25 146 288 65 130 264), lower := (rows 37 98 196 25 146 288 65 130 256), losses := [] }

theorem u628 : Upper (D 7) (R 7) [36,96,192,17,130,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b628 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b629 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 306, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 37 98 196 25 146 288 65 136 258), lower := (rows 37 98 196 25 146 288 65 136 256), losses := [] }

theorem u629 : Upper (D 7) (R 7) [36,96,192,17,130,256,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b629 [(5,8),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b630 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 6, region := 166, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 98 196 25 400 34 65 130 264), lower := (rows 37 98 196 25 400 34 65 130 256), losses := [] }

theorem u630 : Upper (D 7) (R 7) [36,96,192,17,384,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b631 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 306, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,0),(4,0)], upper := (rows 37 98 196 25 400 34 65 136 258), lower := (rows 37 98 196 25 400 34 65 136 256), losses := [] }

theorem u631 : Upper (D 7) (R 7) [36,96,192,17,384,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b631 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b632 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 133, targets := 2 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,1),(1,0),(2,1)], upper := (rows 37 98 196 25 400 40 66 129 258), lower := (rows 37 98 196 25 400 40 66 129 256), losses := [] }

theorem u632 : Upper (D 7) (R 7) [36,96,192,17,384,8,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b632 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b633 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 313, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 98 196 25 400 40 66 130 257), lower := (rows 37 98 196 25 400 40 66 130 256), losses := [] }

theorem u633 : Upper (D 7) (R 7) [36,96,192,17,384,8,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b633 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b634 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 314, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 196 26 152 288 65 129 258), lower := (rows 37 98 196 26 152 288 65 129 256), losses := [] }

theorem u634 : Upper (D 7) (R 7) [36,96,192,18,136,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b634 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b635 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 156, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 196 26 152 288 65 130 257), lower := (rows 37 98 196 26 152 288 65 130 256), losses := [] }

theorem u635 : Upper (D 7) (R 7) [36,96,192,18,136,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b635 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b636 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 314, targets := 1 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 37 98 196 26 400 34 65 129 264), lower := (rows 37 98 196 26 400 34 65 129 256), losses := [] }

theorem u636 : Upper (D 7) (R 7) [36,96,192,18,384,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b637 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 196 26 400 34 65 136 257), lower := (rows 37 98 196 26 400 34 65 136 256), losses := [] }

theorem u637 : Upper (D 7) (R 7) [36,96,192,18,384,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b637 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b638 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 314, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 196 26 400 40 65 129 258), lower := (rows 37 98 196 26 400 40 65 129 256), losses := [] }

theorem u638 : Upper (D 7) (R 7) [36,96,192,18,384,8,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b638 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b639 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 132, targets := 33 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7),(2,0),(2,5)], upper := (rows 37 98 196 26 400 40 65 130 257), lower := (rows 37 98 196 26 400 40 65 130 256), losses := [] }

theorem u639 : Upper (D 7) (R 7) [36,96,192,18,384,8,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b639 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b640 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 314, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 196 138 274 48 65 129 264), lower := (rows 37 98 196 138 274 48 65 129 256), losses := [] }

theorem u640 : Upper (D 7) (R 7) [36,96,192,130,258,16,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b640 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b641 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 140, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 37 98 196 138 274 48 65 136 257), lower := (rows 37 98 196 138 274 48 65 136 256), losses := [] }

theorem u641 : Upper (D 7) (R 7) [36,96,192,130,258,16,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b641 [(5,4),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b642 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 314, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 196 138 280 48 65 129 258), lower := (rows 37 98 196 138 280 48 65 129 256), losses := [] }

theorem u642 : Upper (D 7) (R 7) [36,96,192,130,264,16,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b642 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b643 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 140, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 196 138 280 48 65 130 257), lower := (rows 37 98 196 138 280 48 65 130 256), losses := [] }

theorem u643 : Upper (D 7) (R 7) [36,96,192,130,264,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b643 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b644 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 314, targets := 1 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 37 98 196 152 274 34 65 129 264), lower := (rows 37 98 196 152 274 34 65 129 256), losses := [] }

theorem u644 : Upper (D 7) (R 7) [36,96,192,144,258,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b645 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 98 196 152 274 34 65 136 257), lower := (rows 37 98 196 152 274 34 65 136 256), losses := [] }

theorem u645 : Upper (D 7) (R 7) [36,96,192,144,258,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b645 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b646 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 314, targets := 1 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 37 98 196 152 280 34 65 129 258), lower := (rows 37 98 196 152 280 34 65 129 256), losses := [] }

theorem u646 : Upper (D 7) (R 7) [36,96,192,144,264,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b647 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 6, region := 166, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 37 98 196 152 280 34 65 130 257), lower := (rows 37 98 196 152 280 34 65 130 256), losses := [] }

theorem u647 : Upper (D 7) (R 7) [36,96,192,144,264,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b648 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 261 26 145 34 192 136 320), lower := (rows 37 98 261 26 145 34 192 136 256), losses := [] }

theorem u648 : Upper (D 7) (R 7) [36,96,257,18,129,2,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b648 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b649 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 293, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 261 26 145 34 192 192 264), lower := (rows 37 98 261 26 145 34 192 192 256), losses := [] }

theorem u649 : Upper (D 7) (R 7) [36,96,257,18,129,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b650 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 293, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 98 261 73 146 34 192 136 272), lower := (rows 37 98 261 73 146 34 192 136 256), losses := [] }

theorem u650 : Upper (D 7) (R 7) [36,96,257,65,130,2,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b650 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b651 : PairBound 9 := { available := 8, camps := [{ cop := 6, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 261 73 146 34 192 144 264), lower := (rows 37 98 261 73 146 34 192 144 256), losses := [] }

theorem u651 : Upper (D 7) (R 7) [36,96,257,65,130,2,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b651 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b652 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 98 262 25 146 33 192 136 320), lower := (rows 37 98 262 25 146 33 192 136 256), losses := [] }

theorem u652 : Upper (D 7) (R 7) [36,96,258,17,130,1,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b652 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b653 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 301, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 262 25 146 33 192 192 264), lower := (rows 37 98 262 25 146 33 192 192 256), losses := [] }

theorem u653 : Upper (D 7) (R 7) [36,96,258,17,130,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b654 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 98 262 25 146 160 65 136 320), lower := (rows 37 98 262 25 146 160 65 136 256), losses := [] }

theorem u654 : Upper (D 7) (R 7) [36,96,258,17,130,128,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b654 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b655 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 301, targets := 64 },{ cop := 6, region := 162, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 37 98 262 25 146 160 65 192 264), lower := (rows 37 98 262 25 146 160 65 192 256), losses := [] }

theorem u655 : Upper (D 7) (R 7) [36,96,258,17,130,128,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b656 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(1,7),(4,6)], upper := (rows 37 98 262 88 146 160 65 129 264), lower := (rows 37 98 262 88 146 160 65 129 256), losses := [] }

theorem u656 : Upper (D 7) (R 7) [36,96,258,80,130,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b657 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 262 88 146 160 65 136 257), lower := (rows 37 98 262 88 146 160 65 136 256), losses := [] }

theorem u657 : Upper (D 7) (R 7) [36,96,258,80,130,128,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b657 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b658 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 2, region := 161, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(1,0),(1,7)], upper := (rows 37 98 268 88 146 160 65 129 258), lower := (rows 37 98 268 88 146 160 65 129 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 176 64 128 286), good := (rows 292 354 270 382 434 160 64 160 256) }] }

theorem u658 : Upper (D 7) (R 7) [36,96,264,80,130,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b659 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 365, targets := 2 },{ cop := 6, region := 162, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 37 98 268 88 146 160 65 130 257), lower := (rows 37 98 268 88 146 160 65 130 256), losses := [] }

theorem u659 : Upper (D 7) (R 7) [36,96,264,80,130,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u659
end Delivery.IrregularNine14.P07
