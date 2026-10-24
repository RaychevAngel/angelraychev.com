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

def b11400 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 290 13 200 22 48 192 131 259), lower := (rows 97 290 13 200 22 48 192 128 256), losses := [] }

theorem u11400 : Upper (D 7) (R 7) [96,288,9,192,6,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11400 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11401 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 97 290 13 200 146 48 65 134 262), lower := (rows 97 290 13 200 146 48 65 128 256), losses := [] }

theorem u11401 : Upper (D 7) (R 7) [96,288,9,192,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11401 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11402 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 140, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 97 290 13 200 146 48 66 133 261), lower := (rows 97 290 13 200 146 48 66 128 256), losses := [] }

theorem u11402 : Upper (D 7) (R 7) [96,288,9,192,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11402 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11403 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 97 290 13 200 146 48 68 131 259), lower := (rows 97 290 13 200 146 48 68 128 256), losses := [] }

theorem u11403 : Upper (D 7) (R 7) [96,288,9,192,130,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11403 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11404 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 290 14 28 208 33 65 130 386), lower := (rows 97 290 14 28 208 33 65 128 256), losses := [] }

theorem u11404 : Upper (D 7) (R 7) [96,288,10,20,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11405 : PairBound 9 := { available := 129, camps := [{ cop := 6, region := 177, targets := 2 },{ cop := 8, region := 99, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 290 14 28 208 33 66 129 385), lower := (rows 97 290 14 28 208 33 66 128 256), losses := [] }

theorem u11405 : Upper (D 7) (R 7) [96,288,10,20,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11406 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 290 14 28 208 33 192 131 259), lower := (rows 97 290 14 28 208 33 192 128 256), losses := [] }

theorem u11406 : Upper (D 7) (R 7) [96,288,10,20,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11406 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11407 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 290 14 76 145 48 65 130 386), lower := (rows 97 290 14 76 145 48 65 128 256), losses := [] }

theorem u11407 : Upper (D 7) (R 7) [96,288,10,68,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11407 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11408 : PairBound 9 := { available := 129, camps := [{ cop := 6, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7)], upper := (rows 97 290 14 76 145 48 66 129 385), lower := (rows 97 290 14 76 145 48 66 128 256), losses := [] }

theorem u11408 : Upper (D 7) (R 7) [96,288,10,68,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11408 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11409 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 14 76 145 48 192 131 259), lower := (rows 97 290 14 76 145 48 192 128 256), losses := [] }

theorem u11409 : Upper (D 7) (R 7) [96,288,10,68,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11409 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11410 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 402, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 97 290 14 76 145 160 65 146 274), lower := (rows 97 290 14 76 145 160 65 128 256), losses := [] }

theorem u11410 : Upper (D 7) (R 7) [96,288,10,68,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11411 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 12, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(3,0)], upper := (rows 97 290 14 76 145 160 66 145 273), lower := (rows 97 290 14 76 145 160 66 128 256), losses := [] }

theorem u11411 : Upper (D 7) (R 7) [96,288,10,68,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11412 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 14 76 145 160 80 131 259), lower := (rows 97 290 14 76 145 160 80 128 256), losses := [] }

theorem u11412 : Upper (D 7) (R 7) [96,288,10,68,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11412 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11413 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 0, region := 402, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 97 290 14 76 146 160 65 145 273), lower := (rows 97 290 14 76 146 160 65 128 256), losses := [] }

theorem u11413 : Upper (D 7) (R 7) [96,288,10,68,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11414 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 97 290 14 76 146 160 80 129 257), lower := (rows 97 290 14 76 146 160 80 128 256), losses := [] }

theorem u11414 : Upper (D 7) (R 7) [96,288,10,68,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11414 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11415 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 290 14 88 145 34 65 132 388), lower := (rows 97 290 14 88 145 34 65 128 256), losses := [] }

theorem u11415 : Upper (D 7) (R 7) [96,288,10,80,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11416 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 152, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 290 14 88 145 34 68 129 385), lower := (rows 97 290 14 88 145 34 68 128 256), losses := [] }

theorem u11416 : Upper (D 7) (R 7) [96,288,10,80,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11416 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11417 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 290 14 88 145 34 192 133 261), lower := (rows 97 290 14 88 145 34 192 128 256), losses := [] }

theorem u11417 : Upper (D 7) (R 7) [96,288,10,80,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11418 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 422, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 290 14 88 145 160 65 134 262), lower := (rows 97 290 14 88 145 160 65 128 256), losses := [] }

theorem u11418 : Upper (D 7) (R 7) [96,288,10,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11419 : Route 9 := (fun mask => (mask,id))

def c11419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u11419 : Upper (D 7) (R 7) [96,288,10,80,129,128,2] 13 := by
  apply FastRouting.sound _ _ [96,288,10,80,129,128,2] 13 (by decide) (choices 1) [1,4] r11419 c11419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u851
  · exact u852

def b11420 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(1,6),(1,7),(4,6)], upper := (rows 97 290 14 88 145 160 68 131 259), lower := (rows 97 290 14 88 145 160 68 128 256), losses := [] }

theorem u11420 : Upper (D 7) (R 7) [96,288,10,80,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11420 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11421 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 290 14 88 146 33 65 132 388), lower := (rows 97 290 14 88 146 33 65 128 256), losses := [] }

theorem u11421 : Upper (D 7) (R 7) [96,288,10,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11422 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 97 290 14 88 146 33 68 129 385), lower := (rows 97 290 14 88 146 33 68 128 256), losses := [] }

theorem u11422 : Upper (D 7) (R 7) [96,288,10,80,130,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11422 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11423 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 97 290 14 88 146 33 192 133 261), lower := (rows 97 290 14 88 146 33 192 128 256), losses := [] }

theorem u11423 : Upper (D 7) (R 7) [96,288,10,80,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11424 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 105, targets := 2 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(3,1)], upper := (rows 97 290 14 88 146 160 65 133 261), lower := (rows 97 290 14 88 146 160 65 128 256), losses := [{ target := 7, region := (rows 35 2 20 24 16 32 119 0 276), good := (rows 97 355 335 348 351 97 65 0 256) }] }

theorem u11424 : Upper (D 7) (R 7) [96,288,10,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11425 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 97 290 14 88 146 160 68 129 257), lower := (rows 97 290 14 88 146 160 68 128 256), losses := [] }

theorem u11425 : Upper (D 7) (R 7) [96,288,10,80,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11425 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11426 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 290 14 88 148 33 65 130 386), lower := (rows 97 290 14 88 148 33 65 128 256), losses := [] }

theorem u11426 : Upper (D 7) (R 7) [96,288,10,80,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11427 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 99, targets := 128 },{ cop := 0, region := 386, targets := 64 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,6),(1,7)], upper := (rows 97 290 14 88 148 33 66 129 385), lower := (rows 97 290 14 88 148 33 66 128 256), losses := [] }

theorem u11427 : Upper (D 7) (R 7) [96,288,10,80,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11428 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 290 14 88 148 33 192 131 259), lower := (rows 97 290 14 88 148 33 192 128 256), losses := [] }

theorem u11428 : Upper (D 7) (R 7) [96,288,10,80,132,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11429 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(1,0),(4,0)], upper := (rows 97 290 14 137 82 36 65 144 400), lower := (rows 97 290 14 137 82 36 65 128 256), losses := [] }

theorem u11429 : Upper (D 7) (R 7) [96,288,10,129,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11429 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11430 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 290 14 137 82 36 80 129 385), lower := (rows 97 290 14 137 82 36 80 128 256), losses := [] }

theorem u11430 : Upper (D 7) (R 7) [96,288,10,129,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11430 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11431 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 274, targets := 128 }], pairs := [(1,7),(4,0),(4,7)], upper := (rows 97 290 14 137 82 36 192 145 273), lower := (rows 97 290 14 137 82 36 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 36 200 128 256), good := (rows 96 290 126 200 82 52 192 192 256) }] }

theorem u11431 : Upper (D 7) (R 7) [96,288,10,129,66,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11431 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11432 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 81, targets := 128 },{ cop := 5, region := 73, targets := 2 }], pairs := [(0,1),(0,7),(3,1),(4,7)], upper := (rows 97 290 14 137 82 160 65 148 276), lower := (rows 97 290 14 137 82 160 65 128 256), losses := [] }

theorem u11432 : Upper (D 7) (R 7) [96,288,10,129,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11433 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 161 }], pairs := [(4,0),(4,5),(4,7)], upper := (rows 97 290 14 137 82 160 68 145 273), lower := (rows 97 290 14 137 82 160 68 128 256), losses := [] }

theorem u11433 : Upper (D 7) (R 7) [96,288,10,129,66,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11433 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11434 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 14 137 82 160 80 133 261), lower := (rows 97 290 14 137 82 160 80 128 256), losses := [] }

theorem u11434 : Upper (D 7) (R 7) [96,288,10,129,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11434 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11435 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 418, targets := 65 },{ cop := 5, region := 73, targets := 2 }], pairs := [(0,1),(1,0),(1,6),(3,1)], upper := (rows 97 290 14 137 84 160 65 146 274), lower := (rows 97 290 14 137 84 160 65 128 256), losses := [] }

theorem u11435 : Upper (D 7) (R 7) [96,288,10,129,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11436 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 161 },{ cop := 4, region := 161, targets := 2 }], pairs := [(0,1),(4,0),(4,5),(4,7)], upper := (rows 97 290 14 137 84 160 66 145 273), lower := (rows 97 290 14 137 84 160 66 128 256), losses := [] }

theorem u11436 : Upper (D 7) (R 7) [96,288,10,129,68,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11437 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 97 290 14 137 84 160 80 131 259), lower := (rows 97 290 14 137 84 160 80 128 256), losses := [] }

theorem u11437 : Upper (D 7) (R 7) [96,288,10,129,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11437 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11438 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 97 290 14 137 146 36 65 208 336), lower := (rows 97 290 14 137 146 36 65 128 256), losses := [] }

theorem u11438 : Upper (D 7) (R 7) [96,288,10,129,130,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11438 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11439 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 97 290 14 137 146 36 80 193 321), lower := (rows 97 290 14 137 146 36 80 128 256), losses := [] }

theorem u11439 : Upper (D 7) (R 7) [96,288,10,129,130,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11439 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11440 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 105, targets := 2 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 97 290 14 137 146 48 65 196 324), lower := (rows 97 290 14 137 146 48 65 128 256), losses := [] }

theorem u11440 : Upper (D 7) (R 7) [96,288,10,129,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11440 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11441 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 97 290 14 137 146 48 68 193 321), lower := (rows 97 290 14 137 146 48 68 128 256), losses := [] }

theorem u11441 : Upper (D 7) (R 7) [96,288,10,129,130,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11441 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11442 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 80, targets := 34 },{ cop := 5, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,5)], upper := (rows 97 290 14 137 208 34 65 148 276), lower := (rows 97 290 14 137 208 34 65 128 256), losses := [] }

theorem u11442 : Upper (D 7) (R 7) [96,288,10,129,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11443 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 290 14 137 208 34 68 145 273), lower := (rows 97 290 14 137 208 34 68 128 256), losses := [] }

theorem u11443 : Upper (D 7) (R 7) [96,288,10,129,192,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11443 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11444 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 14 137 208 34 80 133 261), lower := (rows 97 290 14 137 208 34 80 128 256), losses := [] }

theorem u11444 : Upper (D 7) (R 7) [96,288,10,129,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11444 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11445 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 2, region := 97, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 97 290 14 137 208 36 65 146 274), lower := (rows 97 290 14 137 208 36 65 128 256), losses := [] }

theorem u11445 : Upper (D 7) (R 7) [96,288,10,129,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11445 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11446 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 290 14 137 208 36 66 145 273), lower := (rows 97 290 14 137 208 36 66 128 256), losses := [] }

theorem u11446 : Upper (D 7) (R 7) [96,288,10,129,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11446 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11447 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 290 14 137 208 36 80 131 259), lower := (rows 97 290 14 137 208 36 80 128 256), losses := [] }

theorem u11447 : Upper (D 7) (R 7) [96,288,10,129,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11447 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11448 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 140, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 97 290 14 140 82 33 65 144 400), lower := (rows 97 290 14 140 82 33 65 128 256), losses := [] }

theorem u11448 : Upper (D 7) (R 7) [96,288,10,132,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11449 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 14 140 82 33 80 129 385), lower := (rows 97 290 14 140 82 33 80 128 256), losses := [] }

theorem u11449 : Upper (D 7) (R 7) [96,288,10,132,66,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11449 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11450 : PairBound 9 := { available := 17, camps := [{ cop := 6, region := 307, targets := 128 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,7)], upper := (rows 97 290 14 140 82 33 192 145 273), lower := (rows 97 290 14 140 82 33 192 128 256), losses := [] }

theorem u11450 : Upper (D 7) (R 7) [96,288,10,132,66,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11451 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 290 14 140 145 33 66 208 336), lower := (rows 97 290 14 140 145 33 66 128 256), losses := [] }

theorem u11451 : Upper (D 7) (R 7) [96,288,10,132,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11452 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 290 14 140 145 33 80 194 322), lower := (rows 97 290 14 140 145 33 80 128 256), losses := [] }

theorem u11452 : Upper (D 7) (R 7) [96,288,10,132,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11452 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11453 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 97 290 14 140 145 48 65 194 322), lower := (rows 97 290 14 140 145 48 65 128 256), losses := [] }

theorem u11453 : Upper (D 7) (R 7) [96,288,10,132,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11453 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11454 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 355, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(1,7)], upper := (rows 97 290 14 140 145 48 66 193 321), lower := (rows 97 290 14 140 145 48 66 128 256), losses := [] }

theorem u11454 : Upper (D 7) (R 7) [96,288,10,132,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11454 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11455 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 290 14 140 208 33 65 146 274), lower := (rows 97 290 14 140 208 33 65 128 256), losses := [] }

theorem u11455 : Upper (D 7) (R 7) [96,288,10,132,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11456 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 291, targets := 128 },{ cop := 6, region := 177, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(4,1)], upper := (rows 97 290 14 140 208 33 66 145 273), lower := (rows 97 290 14 140 208 33 66 128 256), losses := [] }

theorem u11456 : Upper (D 7) (R 7) [96,288,10,132,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11457 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 14 140 208 33 80 131 259), lower := (rows 97 290 14 140 208 33 80 128 256), losses := [] }

theorem u11457 : Upper (D 7) (R 7) [96,288,10,132,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11457 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11458 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 140, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(3,0)], upper := (rows 97 290 14 152 82 33 65 132 388), lower := (rows 97 290 14 152 82 33 65 128 256), losses := [] }

theorem u11458 : Upper (D 7) (R 7) [96,288,10,144,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11459 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 80, targets := 33 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7),(4,0),(4,5)], upper := (rows 97 290 14 152 82 33 68 129 385), lower := (rows 97 290 14 152 82 33 68 128 256), losses := [] }

theorem u11459 : Upper (D 7) (R 7) [96,288,10,144,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11459 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11459
end Delivery.IrregularNine14.P07
