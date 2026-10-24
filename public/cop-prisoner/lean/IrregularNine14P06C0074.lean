import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0005

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4440 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 146 292 76 81 34 65 164 292), lower := (rows 11 146 292 76 81 34 65 128 256), losses := [] }

theorem u4440 : Upper (D 6) (R 6) [10,144,288,68,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4441 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 146 292 76 81 34 68 161 289), lower := (rows 11 146 292 76 81 34 68 128 256), losses := [] }

theorem u4441 : Upper (D 6) (R 6) [10,144,288,68,65,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4442 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 147, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 146 292 76 81 34 96 133 261), lower := (rows 11 146 292 76 81 34 96 128 256), losses := [] }

theorem u4442 : Upper (D 6) (R 6) [10,144,288,68,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4443 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 146 292 76 112 33 65 134 262), lower := (rows 11 146 292 76 112 33 65 128 256), losses := [] }

theorem u4443 : Upper (D 6) (R 6) [10,144,288,68,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4444 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 292, targets := 66 },{ cop := 0, region := 112, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 146 292 76 112 33 66 133 261), lower := (rows 11 146 292 76 112 33 66 128 256), losses := [] }

theorem u4444 : Upper (D 6) (R 6) [10,144,288,68,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4445 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 146 292 76 112 33 68 131 259), lower := (rows 11 146 292 76 112 33 68 128 256), losses := [] }

theorem u4445 : Upper (D 6) (R 6) [10,144,288,68,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4446 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 112, targets := 4 },{ cop := 0, region := 292, targets := 64 }], pairs := [(2,6),(4,0),(4,2)], upper := (rows 11 146 292 76 112 34 65 133 261), lower := (rows 11 146 292 76 112 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 80 35 64 128 256), good := (rows 42 178 292 92 112 34 112 128 256) }] }

theorem u4446 : Upper (D 6) (R 6) [10,144,288,68,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4447 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 146 292 76 112 34 68 129 257), lower := (rows 11 146 292 76 112 34 68 128 256), losses := [] }

theorem u4447 : Upper (D 6) (R 6) [10,144,288,68,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4448 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 3, region := 260, targets := 1 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 146 292 104 21 33 66 196 324), lower := (rows 11 146 292 104 21 33 66 128 256), losses := [] }

theorem u4448 : Upper (D 6) (R 6) [10,144,288,96,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4449 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(3,0),(3,1)], upper := (rows 11 146 292 104 21 33 68 194 322), lower := (rows 11 146 292 104 21 33 68 128 256), losses := [] }

theorem u4449 : Upper (D 6) (R 6) [10,144,288,96,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4450 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 3, region := 260, targets := 1 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 146 292 104 21 34 65 196 324), lower := (rows 11 146 292 104 21 34 65 128 256), losses := [] }

theorem u4450 : Upper (D 6) (R 6) [10,144,288,96,5,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4451 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(3,0),(3,1)], upper := (rows 11 146 292 104 21 34 68 193 321), lower := (rows 11 146 292 104 21 34 68 128 256), losses := [] }

theorem u4451 : Upper (D 6) (R 6) [10,144,288,96,5,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4452 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 104 22 33 65 196 324), lower := (rows 11 146 292 104 22 33 65 128 256), losses := [] }

theorem u4452 : Upper (D 6) (R 6) [10,144,288,96,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4453 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 72, targets := 1 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 146 292 104 22 33 68 193 321), lower := (rows 11 146 292 104 22 33 68 128 256), losses := [] }

theorem u4453 : Upper (D 6) (R 6) [10,144,288,96,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4454 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 292 104 84 33 65 134 262), lower := (rows 11 146 292 104 84 33 65 128 256), losses := [] }

theorem u4454 : Upper (D 6) (R 6) [10,144,288,96,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4455 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 292, targets := 66 },{ cop := 1, region := 105, targets := 4 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 11 146 292 104 84 33 66 133 261), lower := (rows 11 146 292 104 84 33 66 128 256), losses := [] }

theorem u4455 : Upper (D 6) (R 6) [10,144,288,96,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4456 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 146 292 104 84 33 68 131 259), lower := (rows 11 146 292 104 84 33 68 128 256), losses := [] }

theorem u4456 : Upper (D 6) (R 6) [10,144,288,96,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4457 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 0, region := 292, targets := 64 }], pairs := [(0,2),(2,6),(3,2)], upper := (rows 11 146 292 104 84 34 65 133 261), lower := (rows 11 146 292 104 84 34 65 128 256), losses := [] }

theorem u4457 : Upper (D 6) (R 6) [10,144,288,96,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4458 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 146 292 104 84 34 68 129 257), lower := (rows 11 146 292 104 84 34 68 128 256), losses := [] }

theorem u4458 : Upper (D 6) (R 6) [10,144,288,96,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4459 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 22 44 273 96 65 196 324), lower := (rows 11 162 22 44 273 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 16 117 81 132 260), good := (rows 105 160 508 428 369 96 97 128 256) }] }

theorem u4459 : Upper (D 6) (R 6) [10,160,18,36,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4460 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 104, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 162 22 44 273 96 68 193 321), lower := (rows 11 162 22 44 273 96 68 128 256), losses := [] }

theorem u4460 : Upper (D 6) (R 6) [10,160,18,36,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4461 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 4, region := 230, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 162 22 73 273 36 68 224 352), lower := (rows 11 162 22 73 273 36 68 128 256), losses := [] }

theorem u4461 : Upper (D 6) (R 6) [10,160,18,65,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4462 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 4, region := 230, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 162 22 73 273 36 96 196 324), lower := (rows 11 162 22 73 273 36 96 128 256), losses := [] }

theorem u4462 : Upper (D 6) (R 6) [10,160,18,65,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4463 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 4, region := 230, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 162 22 73 273 96 68 164 292), lower := (rows 11 162 22 73 273 96 68 128 256), losses := [] }

theorem u4463 : Upper (D 6) (R 6) [10,160,18,65,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4464 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 22 73 273 96 96 132 260), lower := (rows 11 162 22 73 273 96 96 128 256), losses := [] }

theorem u4464 : Upper (D 6) (R 6) [10,160,18,65,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4465 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 22 73 276 96 65 164 292), lower := (rows 11 162 22 73 276 96 65 128 256), losses := [] }

theorem u4465 : Upper (D 6) (R 6) [10,160,18,65,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4466 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 22 73 276 96 68 161 289), lower := (rows 11 162 22 73 276 96 68 128 256), losses := [] }

theorem u4466 : Upper (D 6) (R 6) [10,160,18,65,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4467 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 22 73 276 96 96 133 261), lower := (rows 11 162 22 73 276 96 96 128 256), losses := [] }

theorem u4467 : Upper (D 6) (R 6) [10,160,18,65,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4468 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 22 73 304 36 65 196 324), lower := (rows 11 162 22 73 304 36 65 128 256), losses := [] }

theorem u4468 : Upper (D 6) (R 6) [10,160,18,65,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4469 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 162 22 73 304 36 68 193 321), lower := (rows 11 162 22 73 304 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 100 100 136 264), good := (rows 409 224 116 505 368 100 100 128 256) }] }

theorem u4469 : Upper (D 6) (R 6) [10,160,18,65,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4470 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 22 73 304 96 65 132 260), lower := (rows 11 162 22 73 304 96 65 128 256), losses := [] }

theorem u4470 : Upper (D 6) (R 6) [10,160,18,65,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4471 : Route 9 := (fun mask => (mask,id))

def c4471 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4471 : Upper (D 6) (R 6) [10,160,18,65,288,64,4] 13 := by
  apply FastRouting.sound _ _ [10,160,18,65,288,64,4] 13 (by decide) (choices 1) [1,4] r4471 c4471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u332
  · exact u333

def b4472 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 22 73 336 36 65 164 292), lower := (rows 11 162 22 73 336 36 65 128 256), losses := [] }

theorem u4472 : Upper (D 6) (R 6) [10,160,18,65,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4473 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 162 22 73 336 36 68 161 289), lower := (rows 11 162 22 73 336 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 100 100 136 264), good := (rows 409 224 116 505 368 100 100 128 256) }] }

theorem u4473 : Upper (D 6) (R 6) [10,160,18,65,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4474 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,1),(3,2)], upper := (rows 11 162 22 73 336 36 96 133 261), lower := (rows 11 162 22 73 336 36 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 16 36 102 128 256), good := (rows 73 224 116 73 336 100 96 128 256) }] }

theorem u4474 : Upper (D 6) (R 6) [10,160,18,65,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4475 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 435, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 22 76 273 33 68 224 352), lower := (rows 11 162 22 76 273 33 68 128 256), losses := [] }

theorem u4475 : Upper (D 6) (R 6) [10,160,18,68,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4476 : PairBound 9 := { available := 68, camps := [], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 162 22 76 273 33 96 196 324), lower := (rows 11 162 22 76 273 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 98 140 268), good := (rows 458 226 478 460 272 96 96 128 256) },{ target := 1, region := (rows 1 0 4 12 17 49 119 140 268), good := (rows 505 224 508 460 369 113 96 128 256) }] }

theorem u4476 : Upper (D 6) (R 6) [10,160,18,68,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4477 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 3, region := 162, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 162 22 76 273 36 65 224 352), lower := (rows 11 162 22 76 273 36 65 128 256), losses := [] }

theorem u4477 : Upper (D 6) (R 6) [10,160,18,68,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4478 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 104, targets := 3 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 11 162 22 76 273 36 96 193 321), lower := (rows 11 162 22 76 273 36 96 128 256), losses := [{ target := 1, region := (rows 1 0 4 44 17 44 111 145 273), good := (rows 505 232 508 108 465 108 104 128 256) }] }

theorem u4478 : Upper (D 6) (R 6) [10,160,18,68,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4479 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 3, region := 162, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 162 22 76 273 96 65 164 292), lower := (rows 11 162 22 76 273 96 65 128 256), losses := [] }

theorem u4479 : Upper (D 6) (R 6) [10,160,18,68,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4480 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 435, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 22 76 273 96 68 161 289), lower := (rows 11 162 22 76 273 96 68 128 256), losses := [] }

theorem u4480 : Upper (D 6) (R 6) [10,160,18,68,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4481 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 22 76 273 96 96 133 261), lower := (rows 11 162 22 76 273 96 96 128 256), losses := [] }

theorem u4481 : Upper (D 6) (R 6) [10,160,18,68,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4482 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(0,5),(3,5)], upper := (rows 11 162 22 76 276 33 65 224 352), lower := (rows 11 162 22 76 276 33 65 128 256), losses := [] }

theorem u4482 : Upper (D 6) (R 6) [10,160,18,68,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4483 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 162 22 76 276 33 96 193 321), lower := (rows 11 162 22 76 276 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 98 128 256), good := (rows 74 226 94 76 284 96 96 128 256) }] }

theorem u4483 : Upper (D 6) (R 6) [10,160,18,68,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4484 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(0,5),(3,5)], upper := (rows 11 162 22 76 276 96 65 161 289), lower := (rows 11 162 22 76 276 96 65 128 256), losses := [] }

theorem u4484 : Upper (D 6) (R 6) [10,160,18,68,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4485 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 276, targets := 96 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 22 76 276 96 96 129 257), lower := (rows 11 162 22 76 276 96 96 128 256), losses := [] }

theorem u4485 : Upper (D 6) (R 6) [10,160,18,68,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4486 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 162 22 76 304 33 65 196 324), lower := (rows 11 162 22 76 304 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 25 97 97 136 264), good := (rows 505 224 20 508 368 113 113 128 256) }] }

theorem u4486 : Upper (D 6) (R 6) [10,160,18,68,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4487 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 435, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 22 76 304 33 68 193 321), lower := (rows 11 162 22 76 304 33 68 128 256), losses := [] }

theorem u4487 : Upper (D 6) (R 6) [10,160,18,68,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4488 : Route 9 := (fun mask => (mask,id))

def c4488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4488 : Upper (D 6) (R 6) [10,160,18,68,288,64,1] 13 := by
  apply FastRouting.sound _ _ [10,160,18,68,288,64,1] 13 (by decide) (choices 1) [1,4] r4488 c4488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u334
  · exact u335

def b4489 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 435, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 22 76 304 96 68 129 257), lower := (rows 11 162 22 76 304 96 68 128 256), losses := [] }

theorem u4489 : Upper (D 6) (R 6) [10,160,18,68,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4490 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 73, targets := 32 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 162 22 76 336 33 65 164 292), lower := (rows 11 162 22 76 336 33 65 128 256), losses := [] }

theorem u4490 : Upper (D 6) (R 6) [10,160,18,68,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4491 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 435, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 22 76 336 33 68 161 289), lower := (rows 11 162 22 76 336 33 68 128 256), losses := [] }

theorem u4491 : Upper (D 6) (R 6) [10,160,18,68,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4492 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(3,0)], upper := (rows 11 162 22 76 336 33 96 133 261), lower := (rows 11 162 22 76 336 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 32 98 128 256), good := (rows 74 226 94 76 336 96 96 128 256) }] }

theorem u4492 : Upper (D 6) (R 6) [10,160,18,68,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4493 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 22 104 273 36 65 196 324), lower := (rows 11 162 22 104 273 36 65 128 256), losses := [] }

theorem u4493 : Upper (D 6) (R 6) [10,160,18,96,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4494 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 403, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 22 104 273 36 68 193 321), lower := (rows 11 162 22 104 273 36 68 128 256), losses := [] }

theorem u4494 : Upper (D 6) (R 6) [10,160,18,96,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4495 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 22 104 276 33 65 196 324), lower := (rows 11 162 22 104 276 33 65 128 256), losses := [] }

theorem u4495 : Upper (D 6) (R 6) [10,160,18,96,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4496 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 22 104 276 33 68 193 321), lower := (rows 11 162 22 104 276 33 68 128 256), losses := [] }

theorem u4496 : Upper (D 6) (R 6) [10,160,18,96,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4497 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 22 104 336 33 65 132 260), lower := (rows 11 162 22 104 336 33 65 128 256), losses := [] }

theorem u4497 : Upper (D 6) (R 6) [10,160,18,96,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4498 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 22 104 336 33 68 133 261), lower := (rows 11 162 22 104 336 33 68 128 256), losses := [{ target := 2, region := (rows 5 2 0 88 16 101 64 128 256), good := (rows 43 162 59 104 376 33 105 128 256) }] }

theorem u4498 : Upper (D 6) (R 6) [10,160,18,96,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4499 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 22 104 336 36 65 133 261), lower := (rows 11 162 22 104 336 36 65 128 256), losses := [] }

theorem u4499 : Upper (D 6) (R 6) [10,160,18,96,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4499
end Delivery.IrregularNine14.P06
