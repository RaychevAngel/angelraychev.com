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

def b9480 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 200 19 34 96 144 400), lower := (rows 37 266 69 200 19 34 96 128 256), losses := [] }

theorem u9480 : Upper (D 7) (R 7) [36,264,65,192,3,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9481 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 266 69 200 19 34 192 176 304), lower := (rows 37 266 69 200 19 34 192 128 256), losses := [] }

theorem u9481 : Upper (D 7) (R 7) [36,264,65,192,3,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9482 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 117, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 266 69 200 19 48 66 160 416), lower := (rows 37 266 69 200 19 48 66 128 256), losses := [] }

theorem u9482 : Upper (D 7) (R 7) [36,264,65,192,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9482 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9483 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 266 69 200 19 48 96 130 386), lower := (rows 37 266 69 200 19 48 96 128 256), losses := [] }

theorem u9483 : Upper (D 7) (R 7) [36,264,65,192,3,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9483 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9484 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 69 200 19 48 192 162 290), lower := (rows 37 266 69 200 19 48 192 128 256), losses := [] }

theorem u9484 : Upper (D 7) (R 7) [36,264,65,192,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9484 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9485 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,1),(4,6)], upper := (rows 37 266 69 200 145 34 66 176 304), lower := (rows 37 266 69 200 145 34 66 128 256), losses := [] }

theorem u9485 : Upper (D 7) (R 7) [36,264,65,192,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9486 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 37 266 69 200 145 34 80 162 290), lower := (rows 37 266 69 200 145 34 80 128 256), losses := [] }

theorem u9486 : Upper (D 7) (R 7) [36,264,65,192,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9486 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9487 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 200 145 34 96 146 274), lower := (rows 37 266 69 200 145 34 96 128 256), losses := [] }

theorem u9487 : Upper (D 7) (R 7) [36,264,65,192,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9488 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 266 69 200 146 34 65 176 304), lower := (rows 37 266 69 200 146 34 65 128 256), losses := [] }

theorem u9488 : Upper (D 7) (R 7) [36,264,65,192,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9489 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 69 200 146 34 80 161 289), lower := (rows 37 266 69 200 146 34 80 128 256), losses := [] }

theorem u9489 : Upper (D 7) (R 7) [36,264,65,192,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9489 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9490 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 200 146 34 96 145 273), lower := (rows 37 266 69 200 146 34 96 128 256), losses := [] }

theorem u9490 : Upper (D 7) (R 7) [36,264,65,192,130,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9491 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 37 266 69 200 146 48 65 162 290), lower := (rows 37 266 69 200 146 48 65 128 256), losses := [] }

theorem u9491 : Upper (D 7) (R 7) [36,264,65,192,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9491 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9492 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(2,7),(3,0)], upper := (rows 37 266 69 200 146 48 66 161 289), lower := (rows 37 266 69 200 146 48 66 128 256), losses := [] }

theorem u9492 : Upper (D 7) (R 7) [36,264,65,192,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9492 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9493 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 266 69 200 146 48 96 131 259), lower := (rows 37 266 69 200 146 48 96 128 256), losses := [] }

theorem u9493 : Upper (D 7) (R 7) [36,264,65,192,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9493 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9494 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 266 69 200 176 34 65 146 274), lower := (rows 37 266 69 200 176 34 65 128 256), losses := [] }

theorem u9494 : Upper (D 7) (R 7) [36,264,65,192,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9495 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,1),(4,6)], upper := (rows 37 266 69 200 176 34 66 145 273), lower := (rows 37 266 69 200 176 34 66 128 256), losses := [] }

theorem u9495 : Upper (D 7) (R 7) [36,264,65,192,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9496 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 266 69 200 176 34 80 131 259), lower := (rows 37 266 69 200 176 34 80 128 256), losses := [] }

theorem u9496 : Upper (D 7) (R 7) [36,264,65,192,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9496 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9497 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 3, region := 68, targets := 160 }], pairs := [(0,1),(2,5),(2,7),(4,1)], upper := (rows 37 266 70 11 112 160 65 144 400), lower := (rows 37 266 70 11 112 160 65 128 256), losses := [] }

theorem u9497 : Upper (D 7) (R 7) [36,264,66,3,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9498 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 266 70 11 112 160 80 129 385), lower := (rows 37 266 70 11 112 160 80 128 256), losses := [] }

theorem u9498 : Upper (D 7) (R 7) [36,264,66,3,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9498 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9499 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 70 11 112 160 192 145 273), lower := (rows 37 266 70 11 112 160 192 128 256), losses := [] }

theorem u9499 : Upper (D 7) (R 7) [36,264,66,3,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r9500 : Route 9 := (fun mask => (mask,id))

def c9500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u9500 : Upper (D 7) (R 7) [36,264,66,3,129,128,16] 13 := by
  apply FastRouting.sound _ _ [36,264,66,3,129,128,16] 13 (by decide) (choices 1) [32,64] r9500 c9500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u743
  · exact u744

def b9501 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(1,7),(2,0),(4,1)], upper := (rows 37 266 70 11 145 160 96 208 336), lower := (rows 37 266 70 11 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 241 144 272), good := (rows 100 270 70 78 496 224 96 224 256) },{ target := 7, region := (rows 1 18 28 24 16 32 97 0 272), good := (rows 101 270 70 79 351 96 96 0 256) }] }

theorem u9501 : Upper (D 7) (R 7) [36,264,66,3,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9502 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 3, region := 68, targets := 160 }], pairs := [(0,1),(2,5),(2,7),(4,1)], upper := (rows 37 266 70 11 208 160 65 176 304), lower := (rows 37 266 70 11 208 160 65 128 256), losses := [] }

theorem u9502 : Upper (D 7) (R 7) [36,264,66,3,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9503 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 266 70 11 208 160 80 161 289), lower := (rows 37 266 70 11 208 160 80 128 256), losses := [] }

theorem u9503 : Upper (D 7) (R 7) [36,264,66,3,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9503 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9504 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 5, region := 80, targets := 1 }], pairs := [(0,1),(2,0),(4,0),(4,1)], upper := (rows 37 266 70 11 208 160 96 145 273), lower := (rows 37 266 70 11 208 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 176 176 241 128 256), good := (rows 116 270 70 78 240 240 112 240 256) }] }

theorem u9504 : Upper (D 7) (R 7) [36,264,66,3,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9505 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 3, region := 450, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,7)], upper := (rows 37 266 70 25 50 160 65 192 448), lower := (rows 37 266 70 25 50 160 65 128 256), losses := [] }

theorem u9505 : Upper (D 7) (R 7) [36,264,66,17,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9506 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(1,5),(2,0),(2,5)], upper := (rows 37 266 70 25 50 160 192 193 321), lower := (rows 37 266 70 25 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 20 224 224 128 256), good := (rows 116 266 118 28 118 224 224 224 256) }] }

theorem u9506 : Upper (D 7) (R 7) [36,264,66,17,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9507 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 176, targets := 1 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(1,7),(2,5),(4,0)], upper := (rows 37 266 70 25 146 160 65 224 352), lower := (rows 37 266 70 25 146 160 65 128 256), losses := [{ target := 5, region := (rows 1 2 6 8 16 0 73 128 256), good := (rows 69 334 70 89 150 128 65 128 256) },{ target := 7, region := (rows 1 10 14 8 16 32 73 0 257), good := (rows 357 334 70 351 22 32 321 0 256) }] }

theorem u9507 : Upper (D 7) (R 7) [36,264,66,17,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9508 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 161, targets := 2 },{ cop := 4, region := 100, targets := 1 }], pairs := [(0,1),(1,7),(2,0),(2,7)], upper := (rows 37 266 70 25 146 160 96 193 321), lower := (rows 37 266 70 25 146 160 96 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 32 97 0 265), good := (rows 357 270 70 351 18 96 96 0 256) }] }

theorem u9508 : Upper (D 7) (R 7) [36,264,66,17,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9509 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 418, targets := 65 },{ cop := 2, region := 176, targets := 1 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(4,0)], upper := (rows 37 266 70 25 208 160 65 162 290), lower := (rows 37 266 70 25 208 160 65 128 256), losses := [] }

theorem u9509 : Upper (D 7) (R 7) [36,264,66,17,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9510 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 70 25 208 160 66 161 289), lower := (rows 37 266 70 25 208 160 66 128 256), losses := [] }

theorem u9510 : Upper (D 7) (R 7) [36,264,66,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9511 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 80, targets := 3 },{ cop := 2, region := 161, targets := 64 },{ cop := 3, region := 258, targets := 32 }], pairs := [(0,6),(1,5),(4,0),(4,1)], upper := (rows 37 266 70 25 208 160 96 131 259), lower := (rows 37 266 70 25 208 160 96 128 256), losses := [] }

theorem u9511 : Upper (D 7) (R 7) [36,264,66,17,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9512 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 0, region := 80, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(4,1),(4,7)], upper := (rows 37 266 70 26 112 160 65 129 385), lower := (rows 37 266 70 26 112 160 65 128 256), losses := [] }

theorem u9512 : Upper (D 7) (R 7) [36,264,66,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9513 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 70 26 112 160 192 129 257), lower := (rows 37 266 70 26 112 160 192 128 256), losses := [] }

theorem u9513 : Upper (D 7) (R 7) [36,264,66,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9514 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(1,6),(4,1)], upper := (rows 37 266 70 26 208 160 65 161 289), lower := (rows 37 266 70 26 208 160 65 128 256), losses := [{ target := 6, region := (rows 5 18 4 24 16 245 0 197 325), good := (rows 421 266 423 58 442 160 417 160 256) }] }

theorem u9514 : Upper (D 7) (R 7) [36,264,66,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9515 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 2, region := 161, targets := 64 },{ cop := 5, region := 80, targets := 1 }], pairs := [(0,1),(0,6),(4,0),(4,1)], upper := (rows 37 266 70 26 208 160 96 129 257), lower := (rows 37 266 70 26 208 160 96 128 256), losses := [] }

theorem u9515 : Upper (D 7) (R 7) [36,264,66,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9516 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 266 70 42 145 160 65 208 336), lower := (rows 37 266 70 42 145 160 65 128 256), losses := [] }

theorem u9516 : Upper (D 7) (R 7) [36,264,66,34,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9517 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,1),(4,1),(4,5)], upper := (rows 37 266 70 42 145 160 80 193 321), lower := (rows 37 266 70 42 145 160 80 128 256), losses := [] }

theorem u9517 : Upper (D 7) (R 7) [36,264,66,34,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9517 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9518 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 266 70 42 208 160 65 145 273), lower := (rows 37 266 70 42 208 160 65 128 256), losses := [] }

theorem u9518 : Upper (D 7) (R 7) [36,264,66,34,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9519 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 37 266 70 42 208 160 80 129 257), lower := (rows 37 266 70 42 208 160 80 128 256), losses := [] }

theorem u9519 : Upper (D 7) (R 7) [36,264,66,34,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9519 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9520 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1),(4,7)], upper := (rows 37 266 70 56 81 160 65 130 386), lower := (rows 37 266 70 56 81 160 65 128 256), losses := [] }

theorem u9520 : Upper (D 7) (R 7) [36,264,66,48,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9521 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 70 56 81 160 66 129 385), lower := (rows 37 266 70 56 81 160 66 128 256), losses := [] }

theorem u9521 : Upper (D 7) (R 7) [36,264,66,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9522 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(3,6)], upper := (rows 37 266 70 56 81 160 192 131 259), lower := (rows 37 266 70 56 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 100 266 102 120 120 224 224 224 256) }] }

theorem u9522 : Upper (D 7) (R 7) [36,264,66,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9523 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 386, targets := 97 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(1,6)], upper := (rows 37 266 70 56 208 33 65 130 386), lower := (rows 37 266 70 56 208 33 65 128 256), losses := [] }

theorem u9523 : Upper (D 7) (R 7) [36,264,66,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9524 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 185, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,1),(2,0),(3,1),(4,1)], upper := (rows 37 266 70 56 208 33 66 129 385), lower := (rows 37 266 70 56 208 33 66 128 256), losses := [] }

theorem u9524 : Upper (D 7) (R 7) [36,264,66,48,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9525 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 70 56 208 33 192 131 259), lower := (rows 37 266 70 56 208 33 192 128 256), losses := [] }

theorem u9525 : Upper (D 7) (R 7) [36,264,66,48,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9526 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 266 70 73 50 160 65 144 400), lower := (rows 37 266 70 73 50 160 65 128 256), losses := [] }

theorem u9526 : Upper (D 7) (R 7) [36,264,66,65,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9527 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 266 70 73 50 160 80 129 385), lower := (rows 37 266 70 73 50 160 80 128 256), losses := [] }

theorem u9527 : Upper (D 7) (R 7) [36,264,66,65,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9527 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9528 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 3, region := 434, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 37 266 70 73 50 160 192 145 273), lower := (rows 37 266 70 73 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 20 224 224 128 256), good := (rows 116 266 118 104 118 224 224 224 256) }] }

theorem u9528 : Upper (D 7) (R 7) [36,264,66,65,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9529 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 70 73 145 160 66 176 304), lower := (rows 37 266 70 73 145 160 66 128 256), losses := [] }

theorem u9529 : Upper (D 7) (R 7) [36,264,66,65,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9530 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 3, region := 418, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 37 266 70 73 145 160 80 162 290), lower := (rows 37 266 70 73 145 160 80 128 256), losses := [] }

theorem u9530 : Upper (D 7) (R 7) [36,264,66,65,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9530 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9531 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 266 70 73 145 160 96 146 274), lower := (rows 37 266 70 73 145 160 96 128 256), losses := [] }

theorem u9531 : Upper (D 7) (R 7) [36,264,66,65,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9532 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 266 70 73 146 160 65 176 304), lower := (rows 37 266 70 73 146 160 65 128 256), losses := [] }

theorem u9532 : Upper (D 7) (R 7) [36,264,66,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9533 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 169, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 37 266 70 73 146 160 80 161 289), lower := (rows 37 266 70 73 146 160 80 128 256), losses := [] }

theorem u9533 : Upper (D 7) (R 7) [36,264,66,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9533 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9534 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 37 266 70 73 146 160 96 145 273), lower := (rows 37 266 70 73 146 160 96 128 256), losses := [] }

theorem u9534 : Upper (D 7) (R 7) [36,264,66,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9535 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 77, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 37 266 70 88 50 160 65 129 385), lower := (rows 37 266 70 88 50 160 65 128 256), losses := [] }

theorem u9535 : Upper (D 7) (R 7) [36,264,66,80,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9536 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(0,6),(2,0),(4,6)], upper := (rows 37 266 70 88 50 160 192 129 257), lower := (rows 37 266 70 88 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 29 20 224 224 128 256), good := (rows 124 266 126 124 126 224 224 224 256) }] }

theorem u9536 : Upper (D 7) (R 7) [36,264,66,80,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9537 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 3, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(2,0),(4,6)], upper := (rows 37 266 70 88 145 160 65 162 290), lower := (rows 37 266 70 88 145 160 65 128 256), losses := [] }

theorem u9537 : Upper (D 7) (R 7) [36,264,66,80,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9538 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 68, targets := 161 },{ cop := 2, region := 161, targets := 2 }], pairs := [(0,1),(2,0),(2,5),(2,7)], upper := (rows 37 266 70 88 145 160 66 161 289), lower := (rows 37 266 70 88 145 160 66 128 256), losses := [] }

theorem u9538 : Upper (D 7) (R 7) [36,264,66,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9539 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 177, targets := 64 },{ cop := 4, region := 104, targets := 3 }], pairs := [(0,6),(3,0),(3,1),(4,6)], upper := (rows 37 266 70 88 145 160 96 131 259), lower := (rows 37 266 70 88 145 160 96 128 256), losses := [] }

theorem u9539 : Upper (D 7) (R 7) [36,264,66,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u9539
end Delivery.IrregularNine14.P07
