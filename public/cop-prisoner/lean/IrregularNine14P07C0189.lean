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

def b11340 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 13 74 145 48 192 134 262), lower := (rows 97 290 13 74 145 48 192 128 256), losses := [] }

theorem u11340 : Upper (D 7) (R 7) [96,288,9,66,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11340 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11341 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 181, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 97 290 13 74 145 160 66 148 276), lower := (rows 97 290 13 74 145 160 66 128 256), losses := [] }

theorem u11341 : Upper (D 7) (R 7) [96,288,9,66,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11342 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 290 13 74 145 160 68 146 274), lower := (rows 97 290 13 74 145 160 68 128 256), losses := [] }

theorem u11342 : Upper (D 7) (R 7) [96,288,9,66,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11342 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11343 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 13 74 145 160 80 134 262), lower := (rows 97 290 13 74 145 160 80 128 256), losses := [] }

theorem u11343 : Upper (D 7) (R 7) [96,288,9,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11343 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11344 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 97 290 13 74 146 48 65 132 388), lower := (rows 97 290 13 74 146 48 65 128 256), losses := [] }

theorem u11344 : Upper (D 7) (R 7) [96,288,9,66,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11344 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11345 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 97 290 13 74 146 48 68 129 385), lower := (rows 97 290 13 74 146 48 68 128 256), losses := [] }

theorem u11345 : Upper (D 7) (R 7) [96,288,9,66,130,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11345 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11346 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 13 74 146 48 192 133 261), lower := (rows 97 290 13 74 146 48 192 128 256), losses := [] }

theorem u11346 : Upper (D 7) (R 7) [96,288,9,66,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11346 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11347 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 290 13 74 146 160 65 148 276), lower := (rows 97 290 13 74 146 160 65 128 256), losses := [] }

theorem u11347 : Upper (D 7) (R 7) [96,288,9,66,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11348 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 290 13 74 146 160 68 145 273), lower := (rows 97 290 13 74 146 160 68 128 256), losses := [] }

theorem u11348 : Upper (D 7) (R 7) [96,288,9,66,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11348 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11349 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 13 74 146 160 80 133 261), lower := (rows 97 290 13 74 146 160 80 128 256), losses := [] }

theorem u11349 : Upper (D 7) (R 7) [96,288,9,66,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11349 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11350 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 97 290 13 74 148 48 65 130 386), lower := (rows 97 290 13 74 148 48 65 128 256), losses := [] }

theorem u11350 : Upper (D 7) (R 7) [96,288,9,66,132,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11350 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11351 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 290 13 74 148 48 66 129 385), lower := (rows 97 290 13 74 148 48 66 128 256), losses := [] }

theorem u11351 : Upper (D 7) (R 7) [96,288,9,66,132,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11351 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11352 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 13 74 148 48 192 131 259), lower := (rows 97 290 13 74 148 48 192 128 256), losses := [] }

theorem u11352 : Upper (D 7) (R 7) [96,288,9,66,132,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11352 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11353 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 290 13 74 148 160 65 146 274), lower := (rows 97 290 13 74 148 160 65 128 256), losses := [] }

theorem u11353 : Upper (D 7) (R 7) [96,288,9,66,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11354 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 3, region := 181, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 97 290 13 74 148 160 66 145 273), lower := (rows 97 290 13 74 148 160 66 128 256), losses := [] }

theorem u11354 : Upper (D 7) (R 7) [96,288,9,66,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11355 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 13 74 148 160 80 131 259), lower := (rows 97 290 13 74 148 160 80 128 256), losses := [] }

theorem u11355 : Upper (D 7) (R 7) [96,288,9,66,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11355 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11356 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 88 22 160 65 130 386), lower := (rows 97 290 13 88 22 160 65 128 256), losses := [] }

theorem u11356 : Upper (D 7) (R 7) [96,288,9,80,6,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11357 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 88 22 160 66 129 385), lower := (rows 97 290 13 88 22 160 66 128 256), losses := [] }

theorem u11357 : Upper (D 7) (R 7) [96,288,9,80,6,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11358 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 13 88 22 160 192 131 259), lower := (rows 97 290 13 88 22 160 192 128 256), losses := [] }

theorem u11358 : Upper (D 7) (R 7) [96,288,9,80,6,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11359 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 101, targets := 2 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,5)], upper := (rows 97 290 13 138 22 160 65 208 336), lower := (rows 97 290 13 138 22 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 69 144 272), good := (rows 65 258 77 138 478 128 65 128 256) }] }

theorem u11359 : Upper (D 7) (R 7) [96,288,9,130,6,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11360 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 258, targets := 128 },{ cop := 4, region := 225, targets := 2 }], pairs := [(0,1),(1,7),(4,7)], upper := (rows 97 290 13 138 22 160 80 193 321), lower := (rows 97 290 13 138 22 160 80 128 256), losses := [{ target := 7, region := (rows 1 3 4 8 20 32 84 0 261), good := (rows 355 290 351 10 342 32 80 0 256) }] }

theorem u11360 : Upper (D 7) (R 7) [96,288,9,130,6,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11360 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11361 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 290 13 138 82 33 68 144 400), lower := (rows 97 290 13 138 82 33 68 128 256), losses := [] }

theorem u11361 : Upper (D 7) (R 7) [96,288,9,130,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11361 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11362 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 13 138 82 33 80 132 388), lower := (rows 97 290 13 138 82 33 80 128 256), losses := [] }

theorem u11362 : Upper (D 7) (R 7) [96,288,9,130,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11362 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11363 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 80, targets := 33 },{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(2,1),(4,0),(4,5)], upper := (rows 97 290 13 138 82 33 192 148 276), lower := (rows 97 290 13 138 82 33 192 128 256), losses := [] }

theorem u11363 : Upper (D 7) (R 7) [96,288,9,130,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11364 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 290 13 138 82 36 65 144 400), lower := (rows 97 290 13 138 82 36 65 128 256), losses := [] }

theorem u11364 : Upper (D 7) (R 7) [96,288,9,130,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11364 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11365 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 290 13 138 82 36 80 129 385), lower := (rows 97 290 13 138 82 36 80 128 256), losses := [] }

theorem u11365 : Upper (D 7) (R 7) [96,288,9,130,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11365 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11366 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 274, targets := 128 },{ cop := 3, region := 80, targets := 1 }], pairs := [(1,7),(4,0),(4,7)], upper := (rows 97 290 13 138 82 36 192 145 273), lower := (rows 97 290 13 138 82 36 192 128 256), losses := [] }

theorem u11366 : Upper (D 7) (R 7) [96,288,9,130,66,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11366 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11367 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 81, targets := 128 },{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(4,7)], upper := (rows 97 290 13 138 82 160 65 148 276), lower := (rows 97 290 13 138 82 160 65 128 256), losses := [] }

theorem u11367 : Upper (D 7) (R 7) [96,288,9,130,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11368 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 274, targets := 128 },{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(4,7)], upper := (rows 97 290 13 138 82 160 68 145 273), lower := (rows 97 290 13 138 82 160 68 128 256), losses := [] }

theorem u11368 : Upper (D 7) (R 7) [96,288,9,130,66,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11368 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11369 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 13 138 82 160 80 133 261), lower := (rows 97 290 13 138 82 160 80 128 256), losses := [] }

theorem u11369 : Upper (D 7) (R 7) [96,288,9,130,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11369 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11370 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 426, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 97 290 13 138 84 160 65 146 274), lower := (rows 97 290 13 138 84 160 65 128 256), losses := [] }

theorem u11370 : Upper (D 7) (R 7) [96,288,9,130,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11371 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 65, targets := 128 },{ cop := 4, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 290 13 138 84 160 66 145 273), lower := (rows 97 290 13 138 84 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 74 128 256), good := (rows 96 354 124 234 84 160 66 160 256) },{ target := 5, region := (rows 1 2 4 8 20 0 74 132 260), good := (rows 65 322 477 202 468 128 66 128 256) }] }

theorem u11371 : Upper (D 7) (R 7) [96,288,9,130,68,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11372 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 97 290 13 138 84 160 80 131 259), lower := (rows 97 290 13 138 84 160 80 128 256), losses := [] }

theorem u11372 : Upper (D 7) (R 7) [96,288,9,130,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11372 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11373 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 144, targets := 34 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(4,1),(4,5)], upper := (rows 97 290 13 138 145 36 66 208 336), lower := (rows 97 290 13 138 145 36 66 128 256), losses := [] }

theorem u11373 : Upper (D 7) (R 7) [96,288,9,130,129,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11373 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11374 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 97 290 13 138 145 36 80 194 322), lower := (rows 97 290 13 138 145 36 80 128 256), losses := [] }

theorem u11374 : Upper (D 7) (R 7) [96,288,9,130,129,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11374 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11375 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(2,7),(4,5)], upper := (rows 97 290 13 138 145 48 66 196 324), lower := (rows 97 290 13 138 145 48 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 20 0 74 132 260), good := (rows 65 322 477 202 145 16 66 128 256) },{ target := 7, region := (rows 3 2 12 8 16 48 74 0 268), good := (rows 97 355 333 335 49 48 67 0 256) }] }

theorem u11375 : Upper (D 7) (R 7) [96,288,9,130,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11375 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11376 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 97 290 13 138 145 48 68 194 322), lower := (rows 97 290 13 138 145 48 68 128 256), losses := [] }

theorem u11376 : Upper (D 7) (R 7) [96,288,9,130,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11376 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11377 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 4, region := 355, targets := 128 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 97 290 13 138 148 33 66 208 336), lower := (rows 97 290 13 138 148 33 66 128 256), losses := [] }

theorem u11377 : Upper (D 7) (R 7) [96,288,9,130,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11378 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 117, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 290 13 138 148 33 80 194 322), lower := (rows 97 290 13 138 148 33 80 128 256), losses := [] }

theorem u11378 : Upper (D 7) (R 7) [96,288,9,130,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11378 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11379 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 80, targets := 33 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,0),(4,5)], upper := (rows 97 290 13 138 208 33 66 148 276), lower := (rows 97 290 13 138 208 33 66 128 256), losses := [] }

theorem u11379 : Upper (D 7) (R 7) [96,288,9,130,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11380 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 290 13 138 208 33 68 146 274), lower := (rows 97 290 13 138 208 33 68 128 256), losses := [] }

theorem u11380 : Upper (D 7) (R 7) [96,288,9,130,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11380 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11381 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 13 138 208 33 80 134 262), lower := (rows 97 290 13 138 208 33 80 128 256), losses := [] }

theorem u11381 : Upper (D 7) (R 7) [96,288,9,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11381 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11382 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 290 13 138 208 36 65 146 274), lower := (rows 97 290 13 138 208 36 65 128 256), losses := [] }

theorem u11382 : Upper (D 7) (R 7) [96,288,9,130,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11382 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11383 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 34 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(4,1),(4,5)], upper := (rows 97 290 13 138 208 36 66 145 273), lower := (rows 97 290 13 138 208 36 66 128 256), losses := [] }

theorem u11383 : Upper (D 7) (R 7) [96,288,9,130,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11383 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11384 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 290 13 138 208 36 80 131 259), lower := (rows 97 290 13 138 208 36 80 128 256), losses := [] }

theorem u11384 : Upper (D 7) (R 7) [96,288,9,130,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11384 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11385 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 77, targets := 2 },{ cop := 5, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 290 13 140 82 160 65 146 274), lower := (rows 97 290 13 140 82 160 65 128 256), losses := [] }

theorem u11385 : Upper (D 7) (R 7) [96,288,9,132,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11386 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 173, targets := 2 },{ cop := 5, region := 339, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 290 13 140 82 160 66 145 273), lower := (rows 97 290 13 140 82 160 66 128 256), losses := [] }

theorem u11386 : Upper (D 7) (R 7) [96,288,9,132,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11387 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 13 140 82 160 80 131 259), lower := (rows 97 290 13 140 82 160 80 128 256), losses := [] }

theorem u11387 : Upper (D 7) (R 7) [96,288,9,132,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11387 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11388 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 290 13 140 146 48 65 194 322), lower := (rows 97 290 13 140 146 48 65 128 256), losses := [] }

theorem u11388 : Upper (D 7) (R 7) [96,288,9,132,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11388 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11389 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 140, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 97 290 13 140 146 48 66 193 321), lower := (rows 97 290 13 140 146 48 66 128 256), losses := [] }

theorem u11389 : Upper (D 7) (R 7) [96,288,9,132,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11389 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11390 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 101, targets := 2 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(2,1)], upper := (rows 97 290 13 152 22 160 65 194 322), lower := (rows 97 290 13 152 22 160 65 128 256), losses := [] }

theorem u11390 : Upper (D 7) (R 7) [96,288,9,144,6,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11391 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 6, region := 161, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,7)], upper := (rows 97 290 13 152 22 160 66 193 321), lower := (rows 97 290 13 152 22 160 66 128 256), losses := [{ target := 7, region := (rows 35 35 4 8 20 32 119 0 375), good := (rows 355 355 351 344 343 355 323 0 256) }] }

theorem u11391 : Upper (D 7) (R 7) [96,288,9,144,6,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11392 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 290 13 152 82 36 65 130 386), lower := (rows 97 290 13 152 82 36 65 128 256), losses := [] }

theorem u11392 : Upper (D 7) (R 7) [96,288,9,144,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11392 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11393 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 173, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 290 13 152 82 36 66 129 385), lower := (rows 97 290 13 152 82 36 66 128 256), losses := [] }

theorem u11393 : Upper (D 7) (R 7) [96,288,9,144,66,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11393 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11394 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 274, targets := 128 },{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(4,7)], upper := (rows 97 290 13 152 82 36 192 131 259), lower := (rows 97 290 13 152 82 36 192 128 256), losses := [] }

theorem u11394 : Upper (D 7) (R 7) [96,288,9,144,66,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11394 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11395 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 81, targets := 128 },{ cop := 2, region := 418, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(4,7)], upper := (rows 97 290 13 152 82 160 65 134 262), lower := (rows 97 290 13 152 82 160 65 128 256), losses := [] }

theorem u11395 : Upper (D 7) (R 7) [96,288,9,144,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11396 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 173, targets := 2 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,1),(2,1),(3,1),(4,0)], upper := (rows 97 290 13 152 82 160 66 133 261), lower := (rows 97 290 13 152 82 160 66 128 256), losses := [] }

theorem u11396 : Upper (D 7) (R 7) [96,288,9,144,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11397 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 274, targets := 128 },{ cop := 3, region := 101, targets := 2 }], pairs := [(0,1),(1,7),(4,7)], upper := (rows 97 290 13 152 82 160 68 131 259), lower := (rows 97 290 13 152 82 160 68 128 256), losses := [] }

theorem u11397 : Upper (D 7) (R 7) [96,288,9,144,66,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11397 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11398 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 97 290 13 200 22 48 65 130 386), lower := (rows 97 290 13 200 22 48 65 128 256), losses := [] }

theorem u11398 : Upper (D 7) (R 7) [96,288,9,192,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11398 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11399 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 140, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 97 290 13 200 22 48 66 129 385), lower := (rows 97 290 13 200 22 48 66 128 256), losses := [] }

theorem u11399 : Upper (D 7) (R 7) [96,288,9,192,6,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11399 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11399
end Delivery.IrregularNine14.P07
