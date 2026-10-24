import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0105

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21480 : PairBound 9 := { available := 35, camps := [], pairs := [(0,6),(1,2)], upper := (rows 35 74 196 13 276 48 99 163 291), lower := (rows 35 74 196 13 276 48 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 16 48 65 129 257), good := (rows 483 74 192 459 304 48 64 128 256) },{ target := 6, region := (rows 3 2 4 8 24 58 0 131 259), good := (rows 419 443 132 445 308 48 0 128 256) }] }

theorem u21480 : Upper (D 6) (R 6) [34,72,192,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21480 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21481 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 196 13 304 33 86 150 278), lower := (rows 35 74 196 13 304 33 64 128 256), losses := [] }

theorem u21481 : Upper (D 6) (R 6) [34,72,192,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21482 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 13 304 34 85 149 277), lower := (rows 35 74 196 13 304 34 64 128 256), losses := [] }

theorem u21482 : Upper (D 6) (R 6) [34,72,192,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21483 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 272, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 35 74 196 13 304 36 83 147 275), lower := (rows 35 74 196 13 304 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 17 32 73 137 265), good := (rows 499 458 192 475 304 32 64 128 256) }] }

theorem u21483 : Upper (D 6) (R 6) [34,72,192,5,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21484 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 74 196 13 304 48 71 135 263), lower := (rows 35 74 196 13 304 48 64 128 256), losses := [] }

theorem u21484 : Upper (D 6) (R 6) [34,72,192,5,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21484 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21485 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 74 196 25 52 33 326 390 262), lower := (rows 35 74 196 25 52 33 64 128 256), losses := [] }

theorem u21485 : Upper (D 6) (R 6) [34,72,192,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21486 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 25 52 34 325 389 261), lower := (rows 35 74 196 25 52 34 64 128 256), losses := [] }

theorem u21486 : Upper (D 6) (R 6) [34,72,192,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21487 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 74 196 25 52 36 323 387 259), lower := (rows 35 74 196 25 52 36 64 128 256), losses := [] }

theorem u21487 : Upper (D 6) (R 6) [34,72,192,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21488 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 196 25 52 288 71 135 263), lower := (rows 35 74 196 25 52 288 64 128 256), losses := [] }

theorem u21488 : Upper (D 6) (R 6) [34,72,192,17,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21488 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21489 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 74 196 25 274 33 100 164 292), lower := (rows 35 74 196 25 274 33 64 128 256), losses := [] }

theorem u21489 : Upper (D 6) (R 6) [34,72,192,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21490 : Route 9 := (fun mask => (mask,id))

def c21490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21490 : Upper (D 6) (R 6) [34,72,192,17,258,4] 13 := by
  apply FastRouting.sound _ _ [34,72,192,17,258,4] 13 (by decide) (choices 1) [1,4,32] r21490 c21490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6311
  · exact u6312
  · exact u6313

def b21491 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 196 25 276 33 102 166 294), lower := (rows 35 74 196 25 276 33 64 128 256), losses := [] }

theorem u21491 : Upper (D 6) (R 6) [34,72,192,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21492 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 25 276 34 101 165 293), lower := (rows 35 74 196 25 276 34 64 128 256), losses := [] }

theorem u21492 : Upper (D 6) (R 6) [34,72,192,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21493 : Route 9 := (fun mask => (mask,id))

def c21493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21493 : Upper (D 6) (R 6) [34,72,192,17,260,4] 13 := by
  apply FastRouting.sound _ _ [34,72,192,17,260,4] 13 (by decide) (choices 1) [1,2,32] r21493 c21493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6314
  · exact u6315
  · exact u6316

def b21494 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 74 196 25 304 33 70 134 262), lower := (rows 35 74 196 25 304 33 64 128 256), losses := [] }

theorem u21494 : Upper (D 6) (R 6) [34,72,192,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21495 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 25 304 34 69 133 261), lower := (rows 35 74 196 25 304 34 64 128 256), losses := [] }

theorem u21495 : Upper (D 6) (R 6) [34,72,192,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21496 : Route 9 := (fun mask => (mask,id))

def c21496 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21496 : Upper (D 6) (R 6) [34,72,192,17,288,4] 13 := by
  apply FastRouting.sound _ _ [34,72,192,17,288,4] 13 (by decide) (choices 1) [1,2,4] r21496 c21496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6317
  · exact u6318
  · exact u6319

def b21497 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 196 26 273 33 100 164 292), lower := (rows 35 74 196 26 273 33 64 128 256), losses := [] }

theorem u21497 : Upper (D 6) (R 6) [34,72,192,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21498 : Route 9 := (fun mask => (mask,id))

def c21498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21498 : Upper (D 6) (R 6) [34,72,192,18,257,4] 13 := by
  apply FastRouting.sound _ _ [34,72,192,18,257,4] 13 (by decide) (choices 1) [1,4,32] r21498 c21498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6320
  · exact u6321
  · exact u6322

def b21499 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 196 26 276 33 101 165 293), lower := (rows 35 74 196 26 276 33 64 128 256), losses := [] }

theorem u21499 : Upper (D 6) (R 6) [34,72,192,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21500 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 74 196 26 276 36 97 161 289), lower := (rows 35 74 196 26 276 36 64 128 256), losses := [{ target := 6, region := (rows 9 2 4 8 16 52 0 137 265), good := (rows 419 395 164 443 308 36 0 128 256) }] }

theorem u21500 : Upper (D 6) (R 6) [34,72,192,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21501 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 74 196 28 273 33 102 166 294), lower := (rows 35 74 196 28 273 33 64 128 256), losses := [] }

theorem u21501 : Upper (D 6) (R 6) [34,72,192,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21502 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 28 273 34 101 165 293), lower := (rows 35 74 196 28 273 34 64 128 256), losses := [] }

theorem u21502 : Upper (D 6) (R 6) [34,72,192,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21503 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 272, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(0,6),(4,2),(4,6)], upper := (rows 35 74 196 28 273 36 99 163 291), lower := (rows 35 74 196 28 273 36 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 19 44 0 131 259), good := (rows 435 443 164 60 401 36 0 128 256) }] }

theorem u21503 : Upper (D 6) (R 6) [34,72,192,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21504 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 74 196 28 274 33 101 165 293), lower := (rows 35 74 196 28 274 33 64 128 256), losses := [] }

theorem u21504 : Upper (D 6) (R 6) [34,72,192,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21505 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 196, targets := 2 },{ cop := 0, region := 272, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 35 74 196 28 274 36 97 161 289), lower := (rows 35 74 196 28 274 36 64 128 256), losses := [] }

theorem u21505 : Upper (D 6) (R 6) [34,72,192,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21506 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,2),(0,6),(2,5)], upper := (rows 35 74 196 28 304 33 71 135 263), lower := (rows 35 74 196 28 304 33 64 128 256), losses := [] }

theorem u21506 : Upper (D 6) (R 6) [34,72,192,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21507 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 28 304 34 69 133 261), lower := (rows 35 74 196 28 304 34 64 128 256), losses := [] }

theorem u21507 : Upper (D 6) (R 6) [34,72,192,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21508 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 272, targets := 4 },{ cop := 0, region := 196, targets := 32 },{ cop := 0, region := 272, targets := 64 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 74 196 28 304 36 67 131 259), lower := (rows 35 74 196 28 304 36 64 128 256), losses := [] }

theorem u21508 : Upper (D 6) (R 6) [34,72,192,20,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21509 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 196 44 21 33 338 402 274), lower := (rows 35 74 196 44 21 33 64 128 256), losses := [] }

theorem u21509 : Upper (D 6) (R 6) [34,72,192,36,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21510 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 44 21 34 337 401 273), lower := (rows 35 74 196 44 21 34 64 128 256), losses := [] }

theorem u21510 : Upper (D 6) (R 6) [34,72,192,36,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21511 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 74 196 44 21 48 323 387 259), lower := (rows 35 74 196 44 21 48 64 128 256), losses := [] }

theorem u21511 : Upper (D 6) (R 6) [34,72,192,36,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21511 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21512 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 196 44 21 288 83 147 275), lower := (rows 35 74 196 44 21 288 64 128 256), losses := [] }

theorem u21512 : Upper (D 6) (R 6) [34,72,192,36,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21512 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21513 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 196 44 273 33 86 150 278), lower := (rows 35 74 196 44 273 33 64 128 256), losses := [] }

theorem u21513 : Upper (D 6) (R 6) [34,72,192,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21514 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 44 273 34 85 149 277), lower := (rows 35 74 196 44 273 34 64 128 256), losses := [] }

theorem u21514 : Upper (D 6) (R 6) [34,72,192,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21515 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 74 196 44 273 36 83 147 275), lower := (rows 35 74 196 44 273 36 64 128 256), losses := [] }

theorem u21515 : Upper (D 6) (R 6) [34,72,192,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21516 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 196 44 273 48 71 135 263), lower := (rows 35 74 196 44 273 48 64 128 256), losses := [] }

theorem u21516 : Upper (D 6) (R 6) [34,72,192,36,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21516 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21517 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 196 44 274 33 85 149 277), lower := (rows 35 74 196 44 274 33 64 128 256), losses := [] }

theorem u21517 : Upper (D 6) (R 6) [34,72,192,36,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21518 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 74 196 44 274 36 81 145 273), lower := (rows 35 74 196 44 274 36 64 128 256), losses := [] }

theorem u21518 : Upper (D 6) (R 6) [34,72,192,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21519 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 196 44 274 48 69 133 261), lower := (rows 35 74 196 44 274 48 64 128 256), losses := [] }

theorem u21519 : Upper (D 6) (R 6) [34,72,192,36,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21519 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21520 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 196 44 276 33 83 147 275), lower := (rows 35 74 196 44 276 33 64 128 256), losses := [] }

theorem u21520 : Upper (D 6) (R 6) [34,72,192,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21521 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 44 276 34 81 145 273), lower := (rows 35 74 196 44 276 34 64 128 256), losses := [] }

theorem u21521 : Upper (D 6) (R 6) [34,72,192,36,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21522 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 74 196 44 276 48 67 131 259), lower := (rows 35 74 196 44 276 48 64 128 256), losses := [] }

theorem u21522 : Upper (D 6) (R 6) [34,72,192,36,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21522 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21523 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 74 196 56 21 33 326 390 262), lower := (rows 35 74 196 56 21 33 64 128 256), losses := [] }

theorem u21523 : Upper (D 6) (R 6) [34,72,192,48,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21524 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 56 21 34 325 389 261), lower := (rows 35 74 196 56 21 34 64 128 256), losses := [] }

theorem u21524 : Upper (D 6) (R 6) [34,72,192,48,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21525 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 196 56 21 36 323 387 259), lower := (rows 35 74 196 56 21 36 64 128 256), losses := [] }

theorem u21525 : Upper (D 6) (R 6) [34,72,192,48,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21526 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 196 56 21 288 71 135 263), lower := (rows 35 74 196 56 21 288 64 128 256), losses := [] }

theorem u21526 : Upper (D 6) (R 6) [34,72,192,48,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21526 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21527 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 74 196 56 273 33 70 134 262), lower := (rows 35 74 196 56 273 33 64 128 256), losses := [] }

theorem u21527 : Upper (D 6) (R 6) [34,72,192,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21528 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 56 273 34 69 133 261), lower := (rows 35 74 196 56 273 34 64 128 256), losses := [] }

theorem u21528 : Upper (D 6) (R 6) [34,72,192,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21529 : Route 9 := (fun mask => (mask,id))

def c21529 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21529 : Upper (D 6) (R 6) [34,72,192,48,257,4] 13 := by
  apply FastRouting.sound _ _ [34,72,192,48,257,4] 13 (by decide) (choices 1) [1,2,4] r21529 c21529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6323
  · exact u6324
  · exact u6325

def b21530 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 196 56 276 33 71 135 263), lower := (rows 35 74 196 56 276 33 64 128 256), losses := [] }

theorem u21530 : Upper (D 6) (R 6) [34,72,192,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21531 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 56 276 34 69 133 261), lower := (rows 35 74 196 56 276 34 64 128 256), losses := [] }

theorem u21531 : Upper (D 6) (R 6) [34,72,192,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21532 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 196 56 276 36 67 131 259), lower := (rows 35 74 196 56 276 36 64 128 256), losses := [] }

theorem u21532 : Upper (D 6) (R 6) [34,72,192,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21533 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 265 21 34 116 180 308), lower := (rows 35 74 196 265 21 34 64 128 256), losses := [] }

theorem u21533 : Upper (D 6) (R 6) [34,72,192,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21534 : Route 9 := (fun mask => (mask,id))

def c21534 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21534 : Upper (D 6) (R 6) [34,72,192,257,5,4] 13 := by
  apply FastRouting.sound _ _ [34,72,192,257,5,4] 13 (by decide) (choices 1) [2,16,32] r21534 c21534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6326
  · exact u6327
  · exact u6328

def b21535 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 196, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 74 196 265 21 48 102 166 294), lower := (rows 35 74 196 265 21 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 29 8 16 48 65 129 257), good := (rows 486 78 196 462 500 52 64 128 256) }] }

theorem u21535 : Upper (D 6) (R 6) [34,72,192,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21535 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21536 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 212, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 196 265 22 33 116 180 308), lower := (rows 35 74 196 265 22 33 64 128 256), losses := [] }

theorem u21536 : Upper (D 6) (R 6) [34,72,192,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21537 : Route 9 := (fun mask => (mask,id))

def c21537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21537 : Upper (D 6) (R 6) [34,72,192,257,6,4] 13 := by
  apply FastRouting.sound _ _ [34,72,192,257,6,4] 13 (by decide) (choices 1) [1,16,32] r21537 c21537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6329
  · exact u6330
  · exact u6331

def b21538 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 196 265 22 48 101 165 293), lower := (rows 35 74 196 265 22 48 64 128 256), losses := [] }

theorem u21538 : Upper (D 6) (R 6) [34,72,192,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21538 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21539 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 212, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 196 265 52 33 86 150 278), lower := (rows 35 74 196 265 52 33 64 128 256), losses := [] }

theorem u21539 : Upper (D 6) (R 6) [34,72,192,257,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21539
end Delivery.IrregularNine14.P06
