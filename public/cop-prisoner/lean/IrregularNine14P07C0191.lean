import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0014

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11460 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(4,0),(4,5)], upper := (rows 97 290 14 152 82 33 192 133 261), lower := (rows 97 290 14 152 82 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 32 200 128 256), good := (rows 96 290 94 216 82 32 192 192 256) },{ target := 5, region := (rows 1 2 4 8 20 0 200 128 256), good := (rows 65 258 94 216 82 1 192 192 256) }] }

theorem u11460 : Upper (D 7) (R 7) [96,288,10,144,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11461 : Route 9 := (fun mask => (mask,id))

def c11461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11461 : Upper (D 7) (R 7) [96,288,10,144,66,128,1] 13 := by
  apply FastRouting.sound _ _ [96,288,10,144,66,128,1] 13 (by decide) (choices 1) [1,4] r11461 c11461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u853
  · exact u854

def b11462 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 97 290 14 152 82 160 68 129 257), lower := (rows 97 290 14 152 82 160 68 128 256), losses := [] }

theorem u11462 : Upper (D 7) (R 7) [96,288,10,144,66,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11462 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11463 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 290 14 152 84 33 65 130 386), lower := (rows 97 290 14 152 84 33 65 128 256), losses := [] }

theorem u11463 : Upper (D 7) (R 7) [96,288,10,144,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11464 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 80, targets := 33 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,7)], upper := (rows 97 290 14 152 84 33 66 129 385), lower := (rows 97 290 14 152 84 33 66 128 256), losses := [] }

theorem u11464 : Upper (D 7) (R 7) [96,288,10,144,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11465 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 291, targets := 128 },{ cop := 0, region := 258, targets := 64 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(0,7),(1,6),(1,7)], upper := (rows 97 290 14 152 84 33 192 131 259), lower := (rows 97 290 14 152 84 33 192 128 256), losses := [] }

theorem u11465 : Upper (D 7) (R 7) [96,288,10,144,68,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11466 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 49, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 290 14 200 145 33 66 148 276), lower := (rows 97 290 14 200 145 33 66 128 256), losses := [] }

theorem u11466 : Upper (D 7) (R 7) [96,288,10,192,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11467 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,6),(4,6)], upper := (rows 97 290 14 200 145 33 68 146 274), lower := (rows 97 290 14 200 145 33 68 128 256), losses := [] }

theorem u11467 : Upper (D 7) (R 7) [96,288,10,192,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11467 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11468 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 290 14 200 145 33 80 134 262), lower := (rows 97 290 14 200 145 33 80 128 256), losses := [] }

theorem u11468 : Upper (D 7) (R 7) [96,288,10,192,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11468 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11469 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 72, targets := 34 },{ cop := 5, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,5)], upper := (rows 97 290 14 200 145 34 65 148 276), lower := (rows 97 290 14 200 145 34 65 128 256), losses := [] }

theorem u11469 : Upper (D 7) (R 7) [96,288,10,192,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11470 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 290 14 200 145 34 68 145 273), lower := (rows 97 290 14 200 145 34 68 128 256), losses := [] }

theorem u11470 : Upper (D 7) (R 7) [96,288,10,192,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11470 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11471 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 290 14 200 145 34 80 133 261), lower := (rows 97 290 14 200 145 34 80 128 256), losses := [] }

theorem u11471 : Upper (D 7) (R 7) [96,288,10,192,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11471 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11472 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,6),(4,6)], upper := (rows 97 290 14 200 145 36 65 146 274), lower := (rows 97 290 14 200 145 36 65 128 256), losses := [] }

theorem u11472 : Upper (D 7) (R 7) [96,288,10,192,129,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11472 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11473 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 290 14 200 145 36 66 145 273), lower := (rows 97 290 14 200 145 36 66 128 256), losses := [] }

theorem u11473 : Upper (D 7) (R 7) [96,288,10,192,129,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11473 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11474 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 97 290 14 200 145 36 80 131 259), lower := (rows 97 290 14 200 145 36 80 128 256), losses := [] }

theorem u11474 : Upper (D 7) (R 7) [96,288,10,192,129,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11474 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11475 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 290 14 200 145 48 65 134 262), lower := (rows 97 290 14 200 145 48 65 128 256), losses := [] }

theorem u11475 : Upper (D 7) (R 7) [96,288,10,192,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11475 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11476 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 49, targets := 2 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 290 14 200 145 48 66 133 261), lower := (rows 97 290 14 200 145 48 66 128 256), losses := [] }

theorem u11476 : Upper (D 7) (R 7) [96,288,10,192,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11476 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11477 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 97 290 14 200 145 48 68 131 259), lower := (rows 97 290 14 200 145 48 68 128 256), losses := [] }

theorem u11477 : Upper (D 7) (R 7) [96,288,10,192,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11477 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11478 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 290 14 200 146 33 65 148 276), lower := (rows 97 290 14 200 146 33 65 128 256), losses := [] }

theorem u11478 : Upper (D 7) (R 7) [96,288,10,192,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11479 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 97 290 14 200 146 33 68 145 273), lower := (rows 97 290 14 200 146 33 68 128 256), losses := [] }

theorem u11479 : Upper (D 7) (R 7) [96,288,10,192,130,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11479 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11480 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 97 290 14 200 146 33 80 133 261), lower := (rows 97 290 14 200 146 33 80 128 256), losses := [] }

theorem u11480 : Upper (D 7) (R 7) [96,288,10,192,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11480 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11481 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,6),(4,6)], upper := (rows 97 290 14 200 146 36 65 145 273), lower := (rows 97 290 14 200 146 36 65 128 256), losses := [] }

theorem u11481 : Upper (D 7) (R 7) [96,288,10,192,130,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11481 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11482 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 97 290 14 200 146 36 80 129 257), lower := (rows 97 290 14 200 146 36 80 128 256), losses := [] }

theorem u11482 : Upper (D 7) (R 7) [96,288,10,192,130,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11482 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11483 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 105, targets := 2 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 290 14 200 146 48 65 133 261), lower := (rows 97 290 14 200 146 48 65 128 256), losses := [] }

theorem u11483 : Upper (D 7) (R 7) [96,288,10,192,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11483 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11484 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 97 290 14 200 146 48 68 129 257), lower := (rows 97 290 14 200 146 48 68 128 256), losses := [] }

theorem u11484 : Upper (D 7) (R 7) [96,288,10,192,130,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11484 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11485 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 290 14 200 148 33 65 146 274), lower := (rows 97 290 14 200 148 33 65 128 256), losses := [] }

theorem u11485 : Upper (D 7) (R 7) [96,288,10,192,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11486 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 33, targets := 130 },{ cop := 4, region := 355, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(3,0)], upper := (rows 97 290 14 200 148 33 66 145 273), lower := (rows 97 290 14 200 148 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 32 70 128 256), good := (rows 96 354 78 200 220 32 66 128 256) }] }

theorem u11486 : Upper (D 7) (R 7) [96,288,10,192,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11487 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 290 14 200 148 33 80 131 259), lower := (rows 97 290 14 200 148 33 80 128 256), losses := [] }

theorem u11487 : Upper (D 7) (R 7) [96,288,10,192,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11487 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11488 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 181, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 97 290 28 74 145 33 66 132 388), lower := (rows 97 290 28 74 145 33 66 128 256), losses := [] }

theorem u11488 : Upper (D 7) (R 7) [96,288,24,66,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11489 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 394, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 97 290 28 74 145 33 68 130 386), lower := (rows 97 290 28 74 145 33 68 128 256), losses := [] }

theorem u11489 : Upper (D 7) (R 7) [96,288,24,66,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11489 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11490 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 130 },{ cop := 6, region := 49, targets := 2 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 97 290 28 74 145 33 192 134 262), lower := (rows 97 290 28 74 145 33 192 128 256), losses := [{ target := 1, region := (rows 221 0 12 8 208 253 208 128 256), good := (rows 113 288 125 125 241 33 241 241 256) }] }

theorem u11490 : Upper (D 7) (R 7) [96,288,24,66,129,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11491 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 394, targets := 1 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 97 290 28 74 145 36 65 130 386), lower := (rows 97 290 28 74 145 36 65 128 256), losses := [] }

theorem u11491 : Upper (D 7) (R 7) [96,288,24,66,129,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11491 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11492 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 181, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 97 290 28 74 145 36 66 129 385), lower := (rows 97 290 28 74 145 36 66 128 256), losses := [] }

theorem u11492 : Upper (D 7) (R 7) [96,288,24,66,129,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11492 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11493 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(1,6),(1,7),(4,6)], upper := (rows 97 290 28 74 145 36 192 131 259), lower := (rows 97 290 28 74 145 36 192 128 256), losses := [] }

theorem u11493 : Upper (D 7) (R 7) [96,288,24,66,129,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11493 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11494 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 128 },{ cop := 2, region := 418, targets := 65 }], pairs := [(0,7),(1,0),(1,6),(3,7)], upper := (rows 97 290 28 74 145 160 65 134 262), lower := (rows 97 290 28 74 145 160 65 128 256), losses := [] }

theorem u11494 : Upper (D 7) (R 7) [96,288,24,66,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11495 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 181, targets := 2 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(4,1)], upper := (rows 97 290 28 74 145 160 66 133 261), lower := (rows 97 290 28 74 145 160 66 128 256), losses := [] }

theorem u11495 : Upper (D 7) (R 7) [96,288,24,66,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11496 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(1,6),(1,7),(4,6)], upper := (rows 97 290 28 74 145 160 68 131 259), lower := (rows 97 290 28 74 145 160 68 128 256), losses := [] }

theorem u11496 : Upper (D 7) (R 7) [96,288,24,66,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11496 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11497 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 148, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0)], upper := (rows 97 290 28 74 146 33 65 132 388), lower := (rows 97 290 28 74 146 33 65 128 256), losses := [] }

theorem u11497 : Upper (D 7) (R 7) [96,288,24,66,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11498 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 97 290 28 74 146 33 68 129 385), lower := (rows 97 290 28 74 146 33 68 128 256), losses := [] }

theorem u11498 : Upper (D 7) (R 7) [96,288,24,66,130,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11498 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11499 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 97 290 28 74 146 33 192 133 261), lower := (rows 97 290 28 74 146 33 192 128 256), losses := [] }

theorem u11499 : Upper (D 7) (R 7) [96,288,24,66,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11500 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 128 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(3,7)], upper := (rows 97 290 28 74 146 160 65 133 261), lower := (rows 97 290 28 74 146 160 65 128 256), losses := [{ target := 7, region := (rows 35 2 20 26 16 32 123 0 272), good := (rows 97 363 348 75 351 97 65 0 256) }] }

theorem u11500 : Upper (D 7) (R 7) [96,288,24,66,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11501 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 97 290 28 74 146 160 68 129 257), lower := (rows 97 290 28 74 146 160 68 128 256), losses := [] }

theorem u11501 : Upper (D 7) (R 7) [96,288,24,66,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11501 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11502 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 148, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0)], upper := (rows 97 290 28 74 148 33 65 130 386), lower := (rows 97 290 28 74 148 33 65 128 256), losses := [] }

theorem u11502 : Upper (D 7) (R 7) [96,288,24,66,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11503 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 181, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(4,1)], upper := (rows 97 290 28 74 148 33 66 129 385), lower := (rows 97 290 28 74 148 33 66 128 256), losses := [] }

theorem u11503 : Upper (D 7) (R 7) [96,288,24,66,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11504 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 299, targets := 128 },{ cop := 0, region := 258, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(3,7)], upper := (rows 97 290 28 74 148 33 192 131 259), lower := (rows 97 290 28 74 148 33 192 128 256), losses := [] }

theorem u11504 : Upper (D 7) (R 7) [96,288,24,66,132,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11505 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,5)], upper := (rows 97 290 28 137 146 33 66 196 324), lower := (rows 97 290 28 137 146 33 66 128 256), losses := [{ target := 5, region := (rows 1 2 7 41 82 0 82 215 343), good := (rows 477 478 476 397 470 397 470 128 256) }] }

theorem u11505 : Upper (D 7) (R 7) [96,288,24,129,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11506 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 290 28 137 146 33 68 194 322), lower := (rows 97 290 28 137 146 33 68 128 256), losses := [] }

theorem u11506 : Upper (D 7) (R 7) [96,288,24,129,130,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11506 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11507 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 290 28 137 146 36 65 194 322), lower := (rows 97 290 28 137 146 36 65 128 256), losses := [] }

theorem u11507 : Upper (D 7) (R 7) [96,288,24,129,130,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11507 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11508 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 136, targets := 34 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(3,1),(3,5)], upper := (rows 97 290 28 137 146 36 66 193 321), lower := (rows 97 290 28 137 146 36 66 128 256), losses := [] }

theorem u11508 : Upper (D 7) (R 7) [96,288,24,129,130,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11508 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11509 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 290 28 138 208 33 65 134 262), lower := (rows 97 290 28 138 208 33 65 128 256), losses := [] }

theorem u11509 : Upper (D 7) (R 7) [96,288,24,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11510 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 97 290 28 138 208 33 66 133 261), lower := (rows 97 290 28 138 208 33 66 128 256), losses := [] }

theorem u11510 : Upper (D 7) (R 7) [96,288,24,130,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11511 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 290 28 138 208 33 68 131 259), lower := (rows 97 290 28 138 208 33 68 128 256), losses := [] }

theorem u11511 : Upper (D 7) (R 7) [96,288,24,130,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11511 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11512 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6),(4,6)], upper := (rows 97 290 70 137 146 33 68 152 280), lower := (rows 97 290 70 137 146 33 68 128 256), losses := [] }

theorem u11512 : Upper (D 7) (R 7) [96,288,66,129,130,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11512 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11513 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 290 70 137 146 33 72 148 276), lower := (rows 97 290 70 137 146 33 72 128 256), losses := [] }

theorem u11513 : Upper (D 7) (R 7) [96,288,66,129,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11513 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11514 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1)], upper := (rows 97 290 70 137 146 33 80 140 268), lower := (rows 97 290 70 137 146 33 80 128 256), losses := [] }

theorem u11514 : Upper (D 7) (R 7) [96,288,66,129,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11514 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11515 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 97 290 70 137 146 40 65 148 276), lower := (rows 97 290 70 137 146 40 65 128 256), losses := [] }

theorem u11515 : Upper (D 7) (R 7) [96,288,66,129,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11515 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11516 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 410, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 97 290 70 137 146 40 68 145 273), lower := (rows 97 290 70 137 146 40 68 128 256), losses := [] }

theorem u11516 : Upper (D 7) (R 7) [96,288,66,129,130,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11516 [(5,3),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11517 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 68, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 97 290 70 137 146 40 80 133 261), lower := (rows 97 290 70 137 146 40 80 128 256), losses := [] }

theorem u11517 : Upper (D 7) (R 7) [96,288,66,129,130,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11517 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11518 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 97, targets := 2 }], pairs := [(0,1),(0,7),(2,7)], upper := (rows 97 290 70 137 146 48 65 140 268), lower := (rows 97 290 70 137 146 48 65 128 256), losses := [] }

theorem u11518 : Upper (D 7) (R 7) [96,288,66,129,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11518 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11519 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 97 290 70 137 146 48 68 137 265), lower := (rows 97 290 70 137 146 48 68 128 256), losses := [] }

theorem u11519 : Upper (D 7) (R 7) [96,288,66,129,130,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11519 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11519
end Delivery.IrregularNine14.P07
