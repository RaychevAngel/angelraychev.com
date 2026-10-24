import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0011

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8460 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 4, region := 74, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,6)], upper := (rows 37 194 13 88 400 34 66 161 289), lower := (rows 37 194 13 88 400 34 66 128 256), losses := [] }

theorem u8460 : Upper (D 7) (R 7) [36,192,9,80,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8461 : Route 9 := (fun mask => (mask,id))

def c8461 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8461 : Upper (D 7) (R 7) [36,192,9,80,384,2,32] 13 := by
  apply FastRouting.sound _ _ [36,192,9,80,384,2,32] 13 (by decide) (choices 1) [1,2] r8461 c8461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u668
  · exact u669

def b8462 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 194 13 266 81 48 66 160 416), lower := (rows 37 194 13 266 81 48 66 128 256), losses := [] }

theorem u8462 : Upper (D 7) (R 7) [36,192,9,258,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8462 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8463 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 117, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 13 266 81 48 96 130 386), lower := (rows 37 194 13 266 81 48 96 128 256), losses := [] }

theorem u8463 : Upper (D 7) (R 7) [36,192,9,258,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8463 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8464 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 13 266 81 48 192 162 290), lower := (rows 37 194 13 266 81 48 192 128 256), losses := [] }

theorem u8464 : Upper (D 7) (R 7) [36,192,9,258,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8464 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8465 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 7, region := 66, targets := 32 }], pairs := [(0,1),(1,0),(1,5),(3,0)], upper := (rows 37 194 13 280 19 96 66 160 416), lower := (rows 37 194 13 280 19 96 66 128 256), losses := [{ target := 1, region := (rows 17 0 28 24 16 98 64 243 371), good := (rows 421 480 397 413 445 480 480 128 256) }] }

theorem u8465 : Upper (D 7) (R 7) [36,192,9,272,3,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8466 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 13 280 19 96 96 130 386), lower := (rows 37 194 13 280 19 96 96 128 256), losses := [] }

theorem u8466 : Upper (D 7) (R 7) [36,192,9,272,3,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8467 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 13 280 19 96 192 162 290), lower := (rows 37 194 13 280 19 96 192 128 256), losses := [] }

theorem u8467 : Upper (D 7) (R 7) [36,192,9,272,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8468 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 7, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(2,1),(3,0)], upper := (rows 37 194 13 280 81 34 66 160 416), lower := (rows 37 194 13 280 81 34 66 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 64 161 289), good := (rows 421 192 397 284 477 416 64 128 256) }] }

theorem u8468 : Upper (D 7) (R 7) [36,192,9,272,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8469 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 194 13 280 81 34 96 130 386), lower := (rows 37 194 13 280 81 34 96 128 256), losses := [] }

theorem u8469 : Upper (D 7) (R 7) [36,192,9,272,65,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8470 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 13 280 81 34 192 162 290), lower := (rows 37 194 13 280 81 34 192 128 256), losses := [] }

theorem u8470 : Upper (D 7) (R 7) [36,192,9,272,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8471 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 37 194 13 280 81 160 66 162 290), lower := (rows 37 194 13 280 81 160 66 128 256), losses := [{ target := 5, region := (rows 1 162 4 8 21 0 227 128 256), good := (rows 87 194 93 280 81 194 66 194 256) }] }

theorem u8471 : Upper (D 7) (R 7) [36,192,9,272,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8472 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 194 13 280 81 160 96 130 258), lower := (rows 37 194 13 280 81 160 96 128 256), losses := [] }

theorem u8472 : Upper (D 7) (R 7) [36,192,9,272,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8473 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 37 194 13 280 112 34 65 130 386), lower := (rows 37 194 13 280 112 34 65 128 256), losses := [] }

theorem u8473 : Upper (D 7) (R 7) [36,192,9,272,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8474 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 397, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 194 13 280 112 34 66 129 385), lower := (rows 37 194 13 280 112 34 66 128 256), losses := [] }

theorem u8474 : Upper (D 7) (R 7) [36,192,9,272,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8475 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 13 280 112 34 192 131 259), lower := (rows 37 194 13 280 112 34 192 128 256), losses := [] }

theorem u8475 : Upper (D 7) (R 7) [36,192,9,272,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8476 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 37 194 13 280 112 160 65 130 258), lower := (rows 37 194 13 280 112 160 65 128 256), losses := [] }

theorem u8476 : Upper (D 7) (R 7) [36,192,9,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8477 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 82, targets := 1 },{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 48, targets := 2 }], pairs := [(1,0),(1,5),(4,0),(4,1)], upper := (rows 37 194 13 280 112 160 66 131 259), lower := (rows 37 194 13 280 112 160 66 128 256), losses := [] }

theorem u8477 : Upper (D 7) (R 7) [36,192,9,272,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8478 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 37 194 13 328 19 34 80 160 416), lower := (rows 37 194 13 328 19 34 80 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 80 161 289), good := (rows 421 192 397 328 477 416 92 128 256) }] }

theorem u8478 : Upper (D 7) (R 7) [36,192,9,320,3,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8478 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8479 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(3,1)], upper := (rows 37 194 13 328 19 34 96 144 400), lower := (rows 37 194 13 328 19 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 97 144 272), good := (rows 101 192 77 328 477 96 96 128 256) }] }

theorem u8479 : Upper (D 7) (R 7) [36,192,9,320,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8480 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 13 328 19 34 192 176 304), lower := (rows 37 194 13 328 19 34 192 128 256), losses := [] }

theorem u8480 : Upper (D 7) (R 7) [36,192,9,320,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8481 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 7, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 13 328 19 48 66 160 416), lower := (rows 37 194 13 328 19 48 66 128 256), losses := [] }

theorem u8481 : Upper (D 7) (R 7) [36,192,9,320,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8481 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8482 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 13 328 19 48 96 130 386), lower := (rows 37 194 13 328 19 48 96 128 256), losses := [] }

theorem u8482 : Upper (D 7) (R 7) [36,192,9,320,3,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8482 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8483 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 13 328 19 48 192 162 290), lower := (rows 37 194 13 328 19 48 192 128 256), losses := [] }

theorem u8483 : Upper (D 7) (R 7) [36,192,9,320,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8483 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8484 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 490, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 37 194 13 328 19 160 66 176 304), lower := (rows 37 194 13 328 19 160 66 128 256), losses := [{ target := 5, region := (rows 1 162 4 8 17 0 243 128 256), good := (rows 87 194 93 328 83 194 66 194 256) }] }

theorem u8484 : Upper (D 7) (R 7) [36,192,9,320,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8485 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 490, targets := 1 }], pairs := [(0,6),(1,0),(3,0)], upper := (rows 37 194 13 328 19 160 80 162 290), lower := (rows 37 194 13 328 19 160 80 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 242 0 146 274), good := (rows 37 418 13 301 435 160 432 160 256) }] }

theorem u8485 : Upper (D 7) (R 7) [36,192,9,320,3,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8485 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8486 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 490, targets := 1 }], pairs := [(1,0),(2,7),(3,0),(3,7)], upper := (rows 37 194 13 328 19 160 96 146 274), lower := (rows 37 194 13 328 19 160 96 128 256), losses := [{ target := 7, region := (rows 1 2 20 24 16 32 97 0 272), good := (rows 101 66 77 328 351 96 96 0 256) }] }

theorem u8486 : Upper (D 7) (R 7) [36,192,9,320,3,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8487 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,6)], upper := (rows 37 194 13 328 145 34 66 176 304), lower := (rows 37 194 13 328 145 34 66 128 256), losses := [] }

theorem u8487 : Upper (D 7) (R 7) [36,192,9,320,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8488 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 13 328 145 34 80 162 290), lower := (rows 37 194 13 328 145 34 80 128 256), losses := [] }

theorem u8488 : Upper (D 7) (R 7) [36,192,9,320,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8488 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8489 : Route 9 := (fun mask => (mask,id))

def c8489 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8489 : Upper (D 7) (R 7) [36,192,9,320,129,2,32] 13 := by
  apply FastRouting.sound _ _ [36,192,9,320,129,2,32] 13 (by decide) (choices 1) [2,16] r8489 c8489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u670
  · exact u671

def b8490 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 13 328 145 48 66 162 290), lower := (rows 37 194 13 328 145 48 66 128 256), losses := [] }

theorem u8490 : Upper (D 7) (R 7) [36,192,9,320,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8490 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8491 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 13 328 145 48 96 130 258), lower := (rows 37 194 13 328 145 48 96 128 256), losses := [] }

theorem u8491 : Upper (D 7) (R 7) [36,192,9,320,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8491 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8492 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 48, targets := 64 }], pairs := [(1,0),(3,0),(4,0),(4,6)], upper := (rows 37 194 13 328 176 34 65 146 274), lower := (rows 37 194 13 328 176 34 65 128 256), losses := [] }

theorem u8492 : Upper (D 7) (R 7) [36,192,9,320,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8493 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 7, region := 114, targets := 1 }], pairs := [(1,0),(4,0),(4,1),(4,6)], upper := (rows 37 194 13 328 176 34 66 145 273), lower := (rows 37 194 13 328 176 34 66 128 256), losses := [] }

theorem u8493 : Upper (D 7) (R 7) [36,192,9,320,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8494 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 13 328 176 34 80 131 259), lower := (rows 37 194 13 328 176 34 80 128 256), losses := [] }

theorem u8494 : Upper (D 7) (R 7) [36,192,9,320,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8494 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8495 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 434, targets := 1 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(4,0)], upper := (rows 37 194 14 25 336 160 65 162 290), lower := (rows 37 194 14 25 336 160 65 128 256), losses := [{ target := 0, region := (rows 0 82 12 8 82 255 64 222 350), good := (rows 420 498 446 446 498 160 498 160 256) }] }

theorem u8495 : Upper (D 7) (R 7) [36,192,10,17,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8496 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 161, targets := 66 },{ cop := 5, region := 66, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(0,1),(0,6),(1,0),(1,5)], upper := (rows 37 194 14 25 336 160 66 161 289), lower := (rows 37 194 14 25 336 160 66 128 256), losses := [] }

theorem u8496 : Upper (D 7) (R 7) [36,192,10,17,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8497 : Route 9 := (fun mask => (mask,id))

def c8497 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8497 : Upper (D 7) (R 7) [36,192,10,17,320,128,32] 13 := by
  apply FastRouting.sound _ _ [36,192,10,17,320,128,32] 13 (by decide) (choices 1) [1,2] r8497 c8497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u672
  · exact u673

def b8498 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 194 14 73 50 288 65 144 400), lower := (rows 37 194 14 73 50 288 65 128 256), losses := [] }

theorem u8498 : Upper (D 7) (R 7) [36,192,10,65,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8498 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8499 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 14 73 50 288 80 129 385), lower := (rows 37 194 14 73 50 288 80 128 256), losses := [] }

theorem u8499 : Upper (D 7) (R 7) [36,192,10,65,34,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8499 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8500 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 14 73 50 288 192 145 273), lower := (rows 37 194 14 73 50 288 192 128 256), losses := [] }

theorem u8500 : Upper (D 7) (R 7) [36,192,10,65,34,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8500 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8501 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 194 14 73 176 288 65 146 274), lower := (rows 37 194 14 73 176 288 65 128 256), losses := [] }

theorem u8501 : Upper (D 7) (R 7) [36,192,10,65,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8501 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8502 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 194 14 73 176 288 66 145 273), lower := (rows 37 194 14 73 176 288 66 128 256), losses := [] }

theorem u8502 : Upper (D 7) (R 7) [36,192,10,65,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8502 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8503 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 14 73 176 288 80 131 259), lower := (rows 37 194 14 73 176 288 80 128 256), losses := [] }

theorem u8503 : Upper (D 7) (R 7) [36,192,10,65,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8503 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8504 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 194 14 73 274 160 65 176 304), lower := (rows 37 194 14 73 274 160 65 128 256), losses := [] }

theorem u8504 : Upper (D 7) (R 7) [36,192,10,65,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8505 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(4,6)], upper := (rows 37 194 14 73 274 160 80 161 289), lower := (rows 37 194 14 73 274 160 80 128 256), losses := [] }

theorem u8505 : Upper (D 7) (R 7) [36,192,10,65,258,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8505 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8506 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 194 14 73 274 160 96 145 273), lower := (rows 37 194 14 73 274 160 96 128 256), losses := [] }

theorem u8506 : Upper (D 7) (R 7) [36,192,10,65,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8507 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 194 14 73 304 160 65 146 274), lower := (rows 37 194 14 73 304 160 65 128 256), losses := [] }

theorem u8507 : Upper (D 7) (R 7) [36,192,10,65,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8508 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 194 14 73 304 160 66 145 273), lower := (rows 37 194 14 73 304 160 66 128 256), losses := [] }

theorem u8508 : Upper (D 7) (R 7) [36,192,10,65,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8509 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 3, region := 130, targets := 32 }], pairs := [(0,6),(1,5),(4,6)], upper := (rows 37 194 14 73 304 160 80 131 259), lower := (rows 37 194 14 73 304 160 80 128 256), losses := [] }

theorem u8509 : Upper (D 7) (R 7) [36,192,10,65,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8509 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8510 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 194 14 73 400 48 65 162 290), lower := (rows 37 194 14 73 400 48 65 128 256), losses := [] }

theorem u8510 : Upper (D 7) (R 7) [36,192,10,65,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8510 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8511 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 194 14 73 400 48 66 161 289), lower := (rows 37 194 14 73 400 48 66 128 256), losses := [] }

theorem u8511 : Upper (D 7) (R 7) [36,192,10,65,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8511 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8512 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 14 73 400 48 96 131 259), lower := (rows 37 194 14 73 400 48 96 128 256), losses := [] }

theorem u8512 : Upper (D 7) (R 7) [36,192,10,65,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8512 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8513 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 72, targets := 162 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(3,5),(3,7)], upper := (rows 37 194 14 88 273 160 65 162 290), lower := (rows 37 194 14 88 273 160 65 128 256), losses := [] }

theorem u8513 : Upper (D 7) (R 7) [36,192,10,80,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8514 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 194 14 88 273 160 66 161 289), lower := (rows 37 194 14 88 273 160 66 128 256), losses := [] }

theorem u8514 : Upper (D 7) (R 7) [36,192,10,80,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8515 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,6)], upper := (rows 37 194 14 88 273 160 96 131 259), lower := (rows 37 194 14 88 273 160 96 128 256), losses := [{ target := 0, region := (rows 0 162 4 24 16 162 231 128 256), good := (rows 102 226 110 88 344 226 98 226 256) }] }

theorem u8515 : Upper (D 7) (R 7) [36,192,10,80,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8516 : Route 9 := (fun mask => (mask,id))

def c8516 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8516 : Upper (D 7) (R 7) [36,192,10,80,258,128,1] 13 := by
  apply FastRouting.sound _ _ [36,192,10,80,258,128,1] 13 (by decide) (choices 1) [1,32] r8516 c8516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u674
  · exact u675

def b8517 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 2, region := 161, targets := 2 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(1,0),(4,6)], upper := (rows 37 194 14 88 274 160 96 129 257), lower := (rows 37 194 14 88 274 160 96 128 256), losses := [] }

theorem u8517 : Upper (D 7) (R 7) [36,192,10,80,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8518 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7),(3,1),(3,6)], upper := (rows 37 194 14 265 81 48 66 160 416), lower := (rows 37 194 14 265 81 48 66 128 256), losses := [] }

theorem u8518 : Upper (D 7) (R 7) [36,192,10,257,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8518 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8519 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 113, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 194 14 265 81 48 96 130 386), lower := (rows 37 194 14 265 81 48 96 128 256), losses := [] }

theorem u8519 : Upper (D 7) (R 7) [36,192,10,257,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8519 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8519
end Delivery.IrregularNine14.P07
