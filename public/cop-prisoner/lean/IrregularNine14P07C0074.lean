import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0005

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4440 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 161 },{ cop := 4, region := 173, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 13 290 21 200 82 160 66 161 289), lower := (rows 13 290 21 200 82 160 66 128 256), losses := [] }

theorem u4440 : Upper (D 7) (R 7) [12,288,17,192,66,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4441 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 141, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 13 290 21 200 82 160 96 131 259), lower := (rows 13 290 21 200 82 160 96 128 256), losses := [] }

theorem u4441 : Upper (D 7) (R 7) [12,288,17,192,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4442 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 13 290 21 200 112 34 65 130 386), lower := (rows 13 290 21 200 112 34 65 128 256), losses := [] }

theorem u4442 : Upper (D 7) (R 7) [12,288,17,192,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4443 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 141, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 290 21 200 112 34 66 129 385), lower := (rows 13 290 21 200 112 34 66 128 256), losses := [] }

theorem u4443 : Upper (D 7) (R 7) [12,288,17,192,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4444 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 21 200 112 34 192 131 259), lower := (rows 13 290 21 200 112 34 192 128 256), losses := [] }

theorem u4444 : Upper (D 7) (R 7) [12,288,17,192,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4445 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 22 41 81 160 66 192 448), lower := (rows 13 290 22 41 81 160 66 128 256), losses := [] }

theorem u4445 : Upper (D 7) (R 7) [12,288,18,33,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4446 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(0,1),(1,0),(2,0),(3,1)], upper := (rows 13 290 22 41 81 160 192 194 322), lower := (rows 13 290 22 41 81 160 192 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 24 224 224 128 256), good := (rows 29 352 29 121 121 224 224 224 256) }] }

theorem u4446 : Upper (D 7) (R 7) [12,288,18,33,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4447 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 22 73 112 160 65 130 386), lower := (rows 13 290 22 73 112 160 65 128 256), losses := [] }

theorem u4447 : Upper (D 7) (R 7) [12,288,18,65,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4448 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 22 73 112 160 66 129 385), lower := (rows 13 290 22 73 112 160 66 128 256), losses := [] }

theorem u4448 : Upper (D 7) (R 7) [12,288,18,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4449 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 22 73 112 160 192 131 259), lower := (rows 13 290 22 73 112 160 192 128 256), losses := [] }

theorem u4449 : Upper (D 7) (R 7) [12,288,18,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4450 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 2, region := 73, targets := 128 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 290 22 73 145 96 66 160 416), lower := (rows 13 290 22 73 145 96 66 128 256), losses := [] }

theorem u4450 : Upper (D 7) (R 7) [12,288,18,65,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4451 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 105, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 290 22 73 145 96 96 130 386), lower := (rows 13 290 22 73 145 96 96 128 256), losses := [] }

theorem u4451 : Upper (D 7) (R 7) [12,288,18,65,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4452 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 358, targets := 1 },{ cop := 3, region := 290, targets := 128 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,0),(1,7),(2,0),(3,1)], upper := (rows 13 290 22 73 145 96 192 162 290), lower := (rows 13 290 22 73 145 96 192 128 256), losses := [] }

theorem u4452 : Upper (D 7) (R 7) [12,288,18,65,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4453 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 13 290 22 73 176 96 65 130 386), lower := (rows 13 290 22 73 176 96 65 128 256), losses := [] }

theorem u4453 : Upper (D 7) (R 7) [12,288,18,65,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4454 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 2, region := 73, targets := 128 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 290 22 73 176 96 66 129 385), lower := (rows 13 290 22 73 176 96 66 128 256), losses := [] }

theorem u4454 : Upper (D 7) (R 7) [12,288,18,65,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4455 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 6, region := 48, targets := 3 }], pairs := [(0,5),(3,5),(4,0),(4,1)], upper := (rows 13 290 22 73 176 96 192 131 259), lower := (rows 13 290 22 73 176 96 192 128 256), losses := [] }

theorem u4455 : Upper (D 7) (R 7) [12,288,18,65,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4456 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 73, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 290 22 73 208 34 65 160 416), lower := (rows 13 290 22 73 208 34 65 128 256), losses := [] }

theorem u4456 : Upper (D 7) (R 7) [12,288,18,65,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4457 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 105, targets := 128 },{ cop := 3, region := 144, targets := 34 }], pairs := [(0,7),(3,7),(4,1),(4,5)], upper := (rows 13 290 22 73 208 34 96 129 385), lower := (rows 13 290 22 73 208 34 96 128 256), losses := [] }

theorem u4457 : Upper (D 7) (R 7) [12,288,18,65,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4458 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 22 73 208 34 192 161 289), lower := (rows 13 290 22 73 208 34 192 128 256), losses := [] }

theorem u4458 : Upper (D 7) (R 7) [12,288,18,65,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4459 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 73, targets := 162 }], pairs := [(0,1),(0,5),(0,7),(3,1)], upper := (rows 13 290 22 73 208 160 65 162 290), lower := (rows 13 290 22 73 208 160 65 128 256), losses := [] }

theorem u4459 : Upper (D 7) (R 7) [12,288,18,65,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4460 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 160 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 290 22 73 208 160 66 161 289), lower := (rows 13 290 22 73 208 160 66 128 256), losses := [] }

theorem u4460 : Upper (D 7) (R 7) [12,288,18,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4461 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 80, targets := 3 },{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6),(2,0),(4,0),(4,1)], upper := (rows 13 290 22 73 208 160 96 131 259), lower := (rows 13 290 22 73 208 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 176 176 246 128 256), good := (rows 76 374 118 72 240 240 112 240 256) }] }

theorem u4461 : Upper (D 7) (R 7) [12,288,18,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4462 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 22 74 49 160 65 192 448), lower := (rows 13 290 22 74 49 160 65 128 256), losses := [] }

theorem u4462 : Upper (D 7) (R 7) [12,288,18,66,33,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4463 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,5),(3,0),(3,5),(4,1)], upper := (rows 13 290 22 74 49 160 192 193 321), lower := (rows 13 290 22 74 49 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 224 224 128 256), good := (rows 12 362 30 106 112 224 224 224 256) }] }

theorem u4463 : Upper (D 7) (R 7) [12,288,18,66,33,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4464 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 149, targets := 32 },{ cop := 2, region := 105, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(4,5)], upper := (rows 13 290 22 74 145 33 96 192 448), lower := (rows 13 290 22 74 145 33 96 128 256), losses := [] }

theorem u4464 : Upper (D 7) (R 7) [12,288,18,66,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4465 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 458, targets := 1 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,5),(1,0),(3,0),(4,1)], upper := (rows 13 290 22 74 145 33 192 224 352), lower := (rows 13 290 22 74 145 33 192 128 256), losses := [{ target := 5, region := (rows 5 2 4 12 16 0 208 128 256), good := (rows 13 258 95 74 209 1 192 192 256) }] }

theorem u4465 : Upper (D 7) (R 7) [12,288,18,66,129,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4466 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 2, region := 73, targets := 128 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 290 22 74 145 96 65 160 416), lower := (rows 13 290 22 74 145 96 65 128 256), losses := [] }

theorem u4466 : Upper (D 7) (R 7) [12,288,18,66,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4467 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 149, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 13 290 22 74 145 96 96 129 385), lower := (rows 13 290 22 74 145 96 96 128 256), losses := [] }

theorem u4467 : Upper (D 7) (R 7) [12,288,18,66,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4468 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 240, targets := 2 }], pairs := [(0,5),(3,0),(3,5),(4,1)], upper := (rows 13 290 22 74 145 96 192 161 289), lower := (rows 13 290 22 74 145 96 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 252 208 128 256), good := (rows 44 290 126 106 240 96 224 224 256) },{ target := 5, region := (rows 5 2 4 12 16 0 208 128 256), good := (rows 13 258 95 74 209 64 192 192 256) }] }

theorem u4468 : Upper (D 7) (R 7) [12,288,18,66,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4469 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 73, targets := 160 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 290 22 74 145 160 65 224 352), lower := (rows 13 290 22 74 145 160 65 128 256), losses := [] }

theorem u4469 : Upper (D 7) (R 7) [12,288,18,66,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4470 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 149, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 13 290 22 74 145 160 96 193 321), lower := (rows 13 290 22 74 145 160 96 128 256), losses := [] }

theorem u4470 : Upper (D 7) (R 7) [12,288,18,66,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4471 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 2, region := 73, targets := 128 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 290 22 74 176 33 65 192 448), lower := (rows 13 290 22 74 176 33 65 128 256), losses := [] }

theorem u4471 : Upper (D 7) (R 7) [12,288,18,66,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4472 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,5),(3,0),(3,5),(4,1)], upper := (rows 13 290 22 74 176 33 192 193 321), lower := (rows 13 290 22 74 176 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 208 128 256), good := (rows 12 290 94 74 240 32 192 192 256) }] }

theorem u4472 : Upper (D 7) (R 7) [12,288,18,66,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4473 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 2, region := 73, targets := 128 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 290 22 74 176 96 65 129 385), lower := (rows 13 290 22 74 176 96 65 128 256), losses := [] }

theorem u4473 : Upper (D 7) (R 7) [12,288,18,66,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4474 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 6, region := 48, targets := 3 }], pairs := [(0,5),(3,5),(4,0),(4,1)], upper := (rows 13 290 22 74 176 96 192 129 257), lower := (rows 13 290 22 74 176 96 192 128 256), losses := [] }

theorem u4474 : Upper (D 7) (R 7) [12,288,18,66,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4475 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 2, region := 73, targets := 128 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 290 22 74 208 33 65 160 416), lower := (rows 13 290 22 74 208 33 65 128 256), losses := [] }

theorem u4475 : Upper (D 7) (R 7) [12,288,18,66,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4476 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 149, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 13 290 22 74 208 33 96 129 385), lower := (rows 13 290 22 74 208 33 96 128 256), losses := [] }

theorem u4476 : Upper (D 7) (R 7) [12,288,18,66,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4477 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 22 74 208 33 192 161 289), lower := (rows 13 290 22 74 208 33 192 128 256), losses := [] }

theorem u4477 : Upper (D 7) (R 7) [12,288,18,66,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4478 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 160 }], pairs := [(0,5),(0,7),(3,5),(3,7)], upper := (rows 13 290 22 74 208 160 65 161 289), lower := (rows 13 290 22 74 208 160 65 128 256), losses := [] }

theorem u4478 : Upper (D 7) (R 7) [12,288,18,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4479 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 149, targets := 32 },{ cop := 1, region := 72, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 13 290 22 74 208 160 96 129 257), lower := (rows 13 290 22 74 208 160 96 128 256), losses := [] }

theorem u4479 : Upper (D 7) (R 7) [12,288,18,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4480 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 22 104 81 160 65 130 386), lower := (rows 13 290 22 104 81 160 65 128 256), losses := [] }

theorem u4480 : Upper (D 7) (R 7) [12,288,18,96,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4481 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 290 22 104 81 160 66 129 385), lower := (rows 13 290 22 104 81 160 66 128 256), losses := [] }

theorem u4481 : Upper (D 7) (R 7) [12,288,18,96,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4482 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 290 22 104 81 160 192 131 259), lower := (rows 13 290 22 104 81 160 192 128 256), losses := [] }

theorem u4482 : Upper (D 7) (R 7) [12,288,18,96,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4483 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 105, targets := 128 },{ cop := 5, region := 458, targets := 1 }], pairs := [(0,7),(1,0),(3,0),(3,7)], upper := (rows 13 290 22 104 145 33 66 192 448), lower := (rows 13 290 22 104 145 33 66 128 256), losses := [] }

theorem u4483 : Upper (D 7) (R 7) [12,288,18,96,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4484 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 458, targets := 1 },{ cop := 3, region := 258, targets := 128 },{ cop := 4, region := 104, targets := 2 }], pairs := [(1,0),(1,7),(3,0),(3,1)], upper := (rows 13 290 22 104 145 33 192 194 322), lower := (rows 13 290 22 104 145 33 192 128 256), losses := [] }

theorem u4484 : Upper (D 7) (R 7) [12,288,18,96,129,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4485 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 426, targets := 1 },{ cop := 3, region := 258, targets := 128 },{ cop := 4, region := 104, targets := 2 }], pairs := [(1,0),(1,7),(3,0),(3,1)], upper := (rows 13 290 22 104 145 160 65 194 322), lower := (rows 13 290 22 104 145 160 65 128 256), losses := [] }

theorem u4485 : Upper (D 7) (R 7) [12,288,18,96,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4486 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 72, targets := 129 }], pairs := [(0,7),(3,0),(3,7),(4,5)], upper := (rows 13 290 22 104 145 160 66 193 321), lower := (rows 13 290 22 104 145 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 70 129 257), good := (rows 477 322 86 72 401 128 66 128 256) },{ target := 7, region := (rows 5 2 4 10 16 32 70 0 261), good := (rows 333 362 351 104 273 32 74 0 256) }] }

theorem u4486 : Upper (D 7) (R 7) [12,288,18,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4487 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 105, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 290 22 104 208 33 65 130 386), lower := (rows 13 290 22 104 208 33 65 128 256), losses := [] }

theorem u4487 : Upper (D 7) (R 7) [12,288,18,96,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4488 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 72, targets := 129 },{ cop := 0, region := 418, targets := 64 },{ cop := 2, region := 105, targets := 128 }], pairs := [(0,7),(1,6),(3,0),(3,7)], upper := (rows 13 290 22 104 208 33 66 129 385), lower := (rows 13 290 22 104 208 33 66 128 256), losses := [] }

theorem u4488 : Upper (D 7) (R 7) [12,288,18,96,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4489 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 22 104 208 33 192 131 259), lower := (rows 13 290 22 104 208 33 192 128 256), losses := [] }

theorem u4489 : Upper (D 7) (R 7) [12,288,18,96,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4490 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 290 22 200 81 160 65 162 290), lower := (rows 13 290 22 200 81 160 65 128 256), losses := [] }

theorem u4490 : Upper (D 7) (R 7) [12,288,18,192,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4491 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 4, region := 168, targets := 2 }], pairs := [(0,1),(1,6),(2,6),(3,1)], upper := (rows 13 290 22 200 81 160 66 161 289), lower := (rows 13 290 22 200 81 160 66 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 189 64 149 277), good := (rows 429 288 445 232 505 160 64 160 256) }] }

theorem u4491 : Upper (D 7) (R 7) [12,288,18,192,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4492 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 5, region := 72, targets := 3 }], pairs := [(1,6),(2,6),(3,0),(3,1)], upper := (rows 13 290 22 200 81 160 96 131 259), lower := (rows 13 290 22 200 81 160 96 128 256), losses := [] }

theorem u4492 : Upper (D 7) (R 7) [12,288,18,192,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4493 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 290 37 73 146 160 66 208 336), lower := (rows 13 290 37 73 146 160 66 128 256), losses := [] }

theorem u4493 : Upper (D 7) (R 7) [12,288,33,65,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4494 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 290 37 73 146 160 80 194 322), lower := (rows 13 290 37 73 146 160 80 128 256), losses := [] }

theorem u4494 : Upper (D 7) (R 7) [12,288,33,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4494 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4495 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 290 37 74 146 48 65 192 448), lower := (rows 13 290 37 74 146 48 65 128 256), losses := [] }

theorem u4495 : Upper (D 7) (R 7) [12,288,33,66,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4495 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4496 : Route 9 := (fun mask => (mask,id))

def c4496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4496 : Upper (D 7) (R 7) [12,288,33,66,130,16,128] 13 := by
  apply FastRouting.sound _ _ [12,288,33,66,130,16,128] 13 (by decide) (choices 1) [1,64] r4496 c4496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u345
  · exact u346

def b4497 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 290 37 74 146 160 65 208 336), lower := (rows 13 290 37 74 146 160 65 128 256), losses := [] }

theorem u4497 : Upper (D 7) (R 7) [12,288,33,66,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4498 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 165, targets := 2 },{ cop := 4, region := 72, targets := 32 }], pairs := [(0,1),(2,1),(3,5)], upper := (rows 13 290 37 74 146 160 80 193 321), lower := (rows 13 290 37 74 146 160 80 128 256), losses := [] }

theorem u4498 : Upper (D 7) (R 7) [12,288,33,66,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4498 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4499 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 290 37 74 208 48 65 130 386), lower := (rows 13 290 37 74 208 48 65 128 256), losses := [] }

theorem u4499 : Upper (D 7) (R 7) [12,288,33,66,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4499 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4499
end Delivery.IrregularNine14.P07
