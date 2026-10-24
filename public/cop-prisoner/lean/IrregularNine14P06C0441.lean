import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0137
import IrregularNine14P06C0138

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26460 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 276 14 112 34 69 197 325), lower := (rows 41 131 276 14 112 34 64 128 256), losses := [] }

theorem u26460 : Upper (D 6) (R 6) [40,129,272,6,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26461 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 276 14 112 36 67 195 323), lower := (rows 41 131 276 14 112 36 64 128 256), losses := [] }

theorem u26461 : Upper (D 6) (R 6) [40,129,272,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26462 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 41 131 276 14 112 96 71 135 263), lower := (rows 41 131 276 14 112 96 64 128 256), losses := [] }

theorem u26462 : Upper (D 6) (R 6) [40,129,272,6,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26463 : Route 9 := (fun mask => (mask,id))

def c26463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26463 : Upper (D 6) (R 6) [40,129,272,65,6,2] 13 := by
  apply FastRouting.sound _ _ [40,129,272,65,6,2] 13 (by decide) (choices 1) [4,32] r26463 c26463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8247
  · exact u8248

def b26464 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 276 73 22 36 98 226 354), lower := (rows 41 131 276 73 22 36 64 128 256), losses := [] }

theorem u26464 : Upper (D 6) (R 6) [40,129,272,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26465 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 276 73 22 96 102 166 294), lower := (rows 41 131 276 73 22 96 64 128 256), losses := [] }

theorem u26465 : Upper (D 6) (R 6) [40,129,272,65,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26466 : Route 9 := (fun mask => (mask,id))

def c26466 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26466 : Upper (D 6) (R 6) [40,129,272,65,36,2] 13 := by
  apply FastRouting.sound _ _ [40,129,272,65,36,2] 13 (by decide) (choices 1) [2,4] r26466 c26466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8249
  · exact u8250

def b26467 : PairBound 9 := { available := 66, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 131 276 73 52 36 66 194 322), lower := (rows 41 131 276 73 52 36 64 128 256), losses := [] }

theorem u26467 : Upper (D 6) (R 6) [40,129,272,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26468 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 131 276 73 52 96 70 134 262), lower := (rows 41 131 276 73 52 96 64 128 256), losses := [] }

theorem u26468 : Upper (D 6) (R 6) [40,129,272,65,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26469 : Route 9 := (fun mask => (mask,id))

def c26469 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26469 : Upper (D 6) (R 6) [40,129,272,65,68,2] 13 := by
  apply FastRouting.sound _ _ [40,129,272,65,68,2] 13 (by decide) (choices 1) [2,4,32] r26469 c26469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8251
  · exact u8252
  · exact u8253

def b26470 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 276 73 84 36 98 162 290), lower := (rows 41 131 276 73 84 36 64 128 256), losses := [] }

theorem u26470 : Upper (D 6) (R 6) [40,129,272,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26471 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 276 74 21 34 100 228 356), lower := (rows 41 131 276 74 21 34 64 128 256), losses := [] }

theorem u26471 : Upper (D 6) (R 6) [40,129,272,66,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26472 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 276 74 21 36 98 226 354), lower := (rows 41 131 276 74 21 36 64 128 256), losses := [] }

theorem u26472 : Upper (D 6) (R 6) [40,129,272,66,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26473 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 276 74 21 96 102 166 294), lower := (rows 41 131 276 74 21 96 64 128 256), losses := [] }

theorem u26473 : Upper (D 6) (R 6) [40,129,272,66,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26474 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 276 74 22 33 100 228 356), lower := (rows 41 131 276 74 22 33 64 128 256), losses := [] }

theorem u26474 : Upper (D 6) (R 6) [40,129,272,66,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26475 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 276 74 22 36 97 225 353), lower := (rows 41 131 276 74 22 36 64 128 256), losses := [] }

theorem u26475 : Upper (D 6) (R 6) [40,129,272,66,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26476 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 276 74 22 96 101 165 293), lower := (rows 41 131 276 74 22 96 64 128 256), losses := [] }

theorem u26476 : Upper (D 6) (R 6) [40,129,272,66,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26477 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 131 276 74 50 33 68 196 324), lower := (rows 41 131 276 74 50 33 64 128 256), losses := [] }

theorem u26477 : Upper (D 6) (R 6) [40,129,272,66,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26478 : Route 9 := (fun mask => (mask,id))

def c26478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26478 : Upper (D 6) (R 6) [40,129,272,66,34,4] 13 := by
  apply FastRouting.sound _ _ [40,129,272,66,34,4] 13 (by decide) (choices 1) [1,4] r26478 c26478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8254
  · exact u8255

def b26479 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 276 74 50 96 69 133 261), lower := (rows 41 131 276 74 50 96 64 128 256), losses := [] }

theorem u26479 : Upper (D 6) (R 6) [40,129,272,66,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26480 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 276 74 52 33 70 198 326), lower := (rows 41 131 276 74 52 33 64 128 256), losses := [] }

theorem u26480 : Upper (D 6) (R 6) [40,129,272,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26481 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 276 74 52 34 69 197 325), lower := (rows 41 131 276 74 52 34 64 128 256), losses := [] }

theorem u26481 : Upper (D 6) (R 6) [40,129,272,66,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26482 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 131 276 74 52 36 67 195 323), lower := (rows 41 131 276 74 52 36 64 128 256), losses := [] }

theorem u26482 : Upper (D 6) (R 6) [40,129,272,66,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26483 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 276 74 52 96 71 135 263), lower := (rows 41 131 276 74 52 96 64 128 256), losses := [] }

theorem u26483 : Upper (D 6) (R 6) [40,129,272,66,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26484 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 276 74 81 34 100 164 292), lower := (rows 41 131 276 74 81 34 64 128 256), losses := [] }

theorem u26484 : Upper (D 6) (R 6) [40,129,272,66,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26485 : Route 9 := (fun mask => (mask,id))

def c26485 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26485 : Upper (D 6) (R 6) [40,129,272,66,65,4] 13 := by
  apply FastRouting.sound _ _ [40,129,272,66,65,4] 13 (by decide) (choices 1) [2,4,32] r26485 c26485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8256
  · exact u8257
  · exact u8258

def b26486 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 276 74 84 33 102 166 294), lower := (rows 41 131 276 74 84 33 64 128 256), losses := [] }

theorem u26486 : Upper (D 6) (R 6) [40,129,272,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26487 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 276 74 84 34 101 165 293), lower := (rows 41 131 276 74 84 34 64 128 256), losses := [] }

theorem u26487 : Upper (D 6) (R 6) [40,129,272,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26488 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 276 74 84 36 99 163 291), lower := (rows 41 131 276 74 84 36 64 128 256), losses := [] }

theorem u26488 : Upper (D 6) (R 6) [40,129,272,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26489 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 131 276 74 112 33 70 134 262), lower := (rows 41 131 276 74 112 33 64 128 256), losses := [] }

theorem u26489 : Upper (D 6) (R 6) [40,129,272,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26490 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 276 74 112 34 69 133 261), lower := (rows 41 131 276 74 112 34 64 128 256), losses := [] }

theorem u26490 : Upper (D 6) (R 6) [40,129,272,66,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26491 : Route 9 := (fun mask => (mask,id))

def c26491 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26491 : Upper (D 6) (R 6) [40,129,272,66,96,4] 13 := by
  apply FastRouting.sound _ _ [40,129,272,66,96,4] 13 (by decide) (choices 1) [1,2,4] r26491 c26491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8259
  · exact u8260
  · exact u8261

def r26492 : Route 9 := (fun mask => (mask,id))

def c26492 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26492 : Upper (D 6) (R 6) [40,129,272,68,5,2] 13 := by
  apply FastRouting.sound _ _ [40,129,272,68,5,2] 13 (by decide) (choices 1) [2,32] r26492 c26492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8262
  · exact u8263

def b26493 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 276 76 21 96 98 162 290), lower := (rows 41 131 276 76 21 96 64 128 256), losses := [] }

theorem u26493 : Upper (D 6) (R 6) [40,129,272,68,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26494 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 276 76 22 33 98 226 354), lower := (rows 41 131 276 76 22 33 64 128 256), losses := [] }

theorem u26494 : Upper (D 6) (R 6) [40,129,272,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26495 : Route 9 := (fun mask => (mask,id))

def c26495 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26495 : Upper (D 6) (R 6) [40,129,272,68,6,2] 13 := by
  apply FastRouting.sound _ _ [40,129,272,68,6,2] 13 (by decide) (choices 1) [1,32] r26495 c26495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8264
  · exact u8265

def b26496 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 276 76 22 96 99 163 291), lower := (rows 41 131 276 76 22 96 64 128 256), losses := [] }

theorem u26496 : Upper (D 6) (R 6) [40,129,272,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26497 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 332, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 131 276 76 50 33 70 198 326), lower := (rows 41 131 276 76 50 33 64 128 256), losses := [] }

theorem u26497 : Upper (D 6) (R 6) [40,129,272,68,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26498 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 41 131 276 76 50 34 69 197 325), lower := (rows 41 131 276 76 50 34 64 128 256), losses := [] }

theorem u26498 : Upper (D 6) (R 6) [40,129,272,68,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26499 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 276 76 50 36 67 195 323), lower := (rows 41 131 276 76 50 36 64 128 256), losses := [] }

theorem u26499 : Upper (D 6) (R 6) [40,129,272,68,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26500 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 276 76 50 96 71 135 263), lower := (rows 41 131 276 76 50 96 64 128 256), losses := [] }

theorem u26500 : Upper (D 6) (R 6) [40,129,272,68,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26501 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 276 76 82 33 102 166 294), lower := (rows 41 131 276 76 82 33 64 128 256), losses := [] }

theorem u26501 : Upper (D 6) (R 6) [40,129,272,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26502 : Route 9 := (fun mask => (mask,id))

def c26502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26502 : Upper (D 6) (R 6) [40,129,272,68,66,2] 13 := by
  apply FastRouting.sound _ _ [40,129,272,68,66,2] 13 (by decide) (choices 1) [1,4,32] r26502 c26502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8266
  · exact u8267
  · exact u8268

def b26503 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 41 131 276 76 82 36 99 163 291), lower := (rows 41 131 276 76 82 36 64 128 256), losses := [] }

theorem u26503 : Upper (D 6) (R 6) [40,129,272,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26504 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 131 276 76 112 33 70 134 262), lower := (rows 41 131 276 76 112 33 64 128 256), losses := [] }

theorem u26504 : Upper (D 6) (R 6) [40,129,272,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26505 : Route 9 := (fun mask => (mask,id))

def c26505 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26505 : Upper (D 6) (R 6) [40,129,272,68,96,2] 13 := by
  apply FastRouting.sound _ _ [40,129,272,68,96,2] 13 (by decide) (choices 1) [1,2,4] r26505 c26505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8269
  · exact u8270
  · exact u8271

def b26506 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 276 76 112 36 67 131 259), lower := (rows 41 131 276 76 112 36 64 128 256), losses := [] }

theorem u26506 : Upper (D 6) (R 6) [40,129,272,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26507 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 292 14 81 34 84 212 340), lower := (rows 41 131 292 14 81 34 64 128 256), losses := [] }

theorem u26507 : Upper (D 6) (R 6) [40,129,288,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26508 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 131 292 14 81 36 82 210 338), lower := (rows 41 131 292 14 81 36 64 128 256), losses := [] }

theorem u26508 : Upper (D 6) (R 6) [40,129,288,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26509 : PairBound 9 := { available := 70, camps := [], pairs := [(2,0),(3,0)], upper := (rows 41 131 292 14 81 48 70 198 326), lower := (rows 41 131 292 14 81 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 10 16 48 74 138 266), good := (rows 492 462 292 462 116 48 64 128 256) }] }

theorem u26509 : Upper (D 6) (R 6) [40,129,288,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26509 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26510 : Route 9 := (fun mask => (mask,id))

def c26510 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26510 : Upper (D 6) (R 6) [40,129,288,6,65,64] 13 := by
  apply FastRouting.sound _ _ [40,129,288,6,65,64] 13 (by decide) (choices 1) [2,4,16] r26510 c26510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8272
  · exact u8273
  · exact u8274

def b26511 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 292 14 82 33 84 212 340), lower := (rows 41 131 292 14 82 33 64 128 256), losses := [] }

theorem u26511 : Upper (D 6) (R 6) [40,129,288,6,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26512 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 131 292 14 82 36 81 209 337), lower := (rows 41 131 292 14 82 36 64 128 256), losses := [] }

theorem u26512 : Upper (D 6) (R 6) [40,129,288,6,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26513 : Route 9 := (fun mask => (mask,id))

def c26513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26513 : Upper (D 6) (R 6) [40,129,288,6,66,16] 13 := by
  apply FastRouting.sound _ _ [40,129,288,6,66,16] 13 (by decide) (choices 1) [1,4] r26513 c26513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8275
  · exact u8276

def r26514 : Route 9 := (fun mask => (mask,id))

def c26514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26514 : Upper (D 6) (R 6) [40,129,288,6,66,64] 13 := by
  apply FastRouting.sound _ _ [40,129,288,6,66,64] 13 (by decide) (choices 1) [1,4,16] r26514 c26514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8277
  · exact u8278
  · exact u8279

def b26515 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 292 14 84 33 82 210 338), lower := (rows 41 131 292 14 84 33 64 128 256), losses := [] }

theorem u26515 : Upper (D 6) (R 6) [40,129,288,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26516 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 292 14 84 34 81 209 337), lower := (rows 41 131 292 14 84 34 64 128 256), losses := [] }

theorem u26516 : Upper (D 6) (R 6) [40,129,288,6,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26517 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 194, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 41 131 292 14 84 48 67 195 323), lower := (rows 41 131 292 14 84 48 64 128 256), losses := [] }

theorem u26517 : Upper (D 6) (R 6) [40,129,288,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26517 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26518 : Route 9 := (fun mask => (mask,id))

def c26518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26518 : Upper (D 6) (R 6) [40,129,288,6,68,64] 13 := by
  apply FastRouting.sound _ _ [40,129,288,6,68,64] 13 (by decide) (choices 1) [1,2,16] r26518 c26518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8280
  · exact u8281
  · exact u8282

def b26519 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 131 292 25 82 34 68 196 324), lower := (rows 41 131 292 25 82 34 64 128 256), losses := [] }

theorem u26519 : Upper (D 6) (R 6) [40,129,288,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u26519
end Delivery.IrregularNine14.P06
