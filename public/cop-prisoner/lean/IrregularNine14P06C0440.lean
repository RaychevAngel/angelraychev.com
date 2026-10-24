import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0137

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r26400 : Route 9 := (fun mask => (mask,id))

def c26400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26400 : Upper (D 6) (R 6) [40,129,258,66,5,16] 13 := by
  apply FastRouting.sound _ _ [40,129,258,66,5,16] 13 (by decide) (choices 1) [4,32] r26400 c26400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8224
  · exact u8225

def b26401 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 262 74 21 96 116 180 308), lower := (rows 41 131 262 74 21 96 64 128 256), losses := [] }

theorem u26401 : Upper (D 6) (R 6) [40,129,258,66,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26402 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 262 74 52 33 84 212 340), lower := (rows 41 131 262 74 52 33 64 128 256), losses := [] }

theorem u26402 : Upper (D 6) (R 6) [40,129,258,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26403 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 131 262 74 52 36 81 209 337), lower := (rows 41 131 262 74 52 36 64 128 256), losses := [] }

theorem u26403 : Upper (D 6) (R 6) [40,129,258,66,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26404 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 131 262 74 52 48 69 197 325), lower := (rows 41 131 262 74 52 48 64 128 256), losses := [] }

theorem u26404 : Upper (D 6) (R 6) [40,129,258,66,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26404 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26405 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 262 74 52 96 85 149 277), lower := (rows 41 131 262 74 52 96 64 128 256), losses := [] }

theorem u26405 : Upper (D 6) (R 6) [40,129,258,66,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26406 : Route 9 := (fun mask => (mask,id))

def c26406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26406 : Upper (D 6) (R 6) [40,129,258,66,65,4] 13 := by
  apply FastRouting.sound _ _ [40,129,258,66,65,4] 13 (by decide) (choices 1) [4,16,32] r26406 c26406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8226
  · exact u8227
  · exact u8228

def b26407 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 131 262 74 81 48 100 164 292), lower := (rows 41 131 262 74 81 48 64 128 256), losses := [] }

theorem u26407 : Upper (D 6) (R 6) [40,129,258,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26407 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26408 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 262 74 84 33 116 180 308), lower := (rows 41 131 262 74 84 33 64 128 256), losses := [] }

theorem u26408 : Upper (D 6) (R 6) [40,129,258,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26409 : Route 9 := (fun mask => (mask,id))

def c26409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26409 : Upper (D 6) (R 6) [40,129,258,66,68,4] 13 := by
  apply FastRouting.sound _ _ [40,129,258,66,68,4] 13 (by decide) (choices 1) [1,16,32] r26409 c26409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8229
  · exact u8230
  · exact u8231

def b26410 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 41 131 262 74 84 48 101 165 293), lower := (rows 41 131 262 74 84 48 64 128 256), losses := [] }

theorem u26410 : Upper (D 6) (R 6) [40,129,258,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26410 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26411 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 131 262 74 112 33 84 148 276), lower := (rows 41 131 262 74 112 33 64 128 256), losses := [] }

theorem u26411 : Upper (D 6) (R 6) [40,129,258,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26412 : Route 9 := (fun mask => (mask,id))

def c26412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26412 : Upper (D 6) (R 6) [40,129,258,66,96,4] 13 := by
  apply FastRouting.sound _ _ [40,129,258,66,96,4] 13 (by decide) (choices 1) [1,4,16] r26412 c26412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8232
  · exact u8233
  · exact u8234

def b26413 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 131 262 74 112 48 69 133 261), lower := (rows 41 131 262 74 112 48 64 128 256), losses := [] }

theorem u26413 : Upper (D 6) (R 6) [40,129,258,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26413 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26414 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 226, targets := 4 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 41 131 262 76 21 34 112 240 368), lower := (rows 41 131 262 76 21 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 38 80 144 272), good := (rows 40 162 294 108 508 34 64 128 256) },{ target := 2, region := (rows 9 18 0 8 16 54 80 144 272), good := (rows 41 163 290 105 499 34 64 128 256) }] }

theorem u26414 : Upper (D 6) (R 6) [40,129,258,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26415 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 131 262 76 21 48 98 226 354), lower := (rows 41 131 262 76 21 48 64 128 256), losses := [] }

theorem u26415 : Upper (D 6) (R 6) [40,129,258,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26415 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26416 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 262 76 21 96 114 178 306), lower := (rows 41 131 262 76 21 96 64 128 256), losses := [] }

theorem u26416 : Upper (D 6) (R 6) [40,129,258,68,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26417 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 332, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 131 262 76 50 33 84 212 340), lower := (rows 41 131 262 76 50 33 64 128 256), losses := [] }

theorem u26417 : Upper (D 6) (R 6) [40,129,258,68,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26418 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,2),(4,0),(4,2)], upper := (rows 41 131 262 76 50 36 81 209 337), lower := (rows 41 131 262 76 50 36 64 128 256), losses := [] }

theorem u26418 : Upper (D 6) (R 6) [40,129,258,68,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26419 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 41 131 262 76 50 48 69 197 325), lower := (rows 41 131 262 76 50 48 64 128 256), losses := [] }

theorem u26419 : Upper (D 6) (R 6) [40,129,258,68,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26419 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26420 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 262 76 50 96 85 149 277), lower := (rows 41 131 262 76 50 96 64 128 256), losses := [] }

theorem u26420 : Upper (D 6) (R 6) [40,129,258,68,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26421 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 131 262 76 52 33 82 210 338), lower := (rows 41 131 262 76 52 33 64 128 256), losses := [] }

theorem u26421 : Upper (D 6) (R 6) [40,129,258,68,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26422 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 48, targets := 65 },{ cop := 4, region := 73, targets := 2 }], pairs := [(0,1),(4,0),(4,6)], upper := (rows 41 131 262 76 52 34 81 209 337), lower := (rows 41 131 262 76 52 34 64 128 256), losses := [] }

theorem u26422 : Upper (D 6) (R 6) [40,129,258,68,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26423 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 131 262 76 52 48 67 195 323), lower := (rows 41 131 262 76 52 48 64 128 256), losses := [] }

theorem u26423 : Upper (D 6) (R 6) [40,129,258,68,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26423 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26424 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 262 76 52 96 83 147 275), lower := (rows 41 131 262 76 52 96 64 128 256), losses := [] }

theorem u26424 : Upper (D 6) (R 6) [40,129,258,68,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26425 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(0,2),(1,6),(2,6)], upper := (rows 41 131 262 76 81 34 116 180 308), lower := (rows 41 131 262 76 81 34 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 24 38 64 128 256), good := (rows 57 163 290 121 81 34 64 128 256) }] }

theorem u26425 : Upper (D 6) (R 6) [40,129,258,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26426 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 262 76 81 36 114 178 306), lower := (rows 41 131 262 76 81 36 64 128 256), losses := [] }

theorem u26426 : Upper (D 6) (R 6) [40,129,258,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26427 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 131 262 76 81 48 102 166 294), lower := (rows 41 131 262 76 81 48 64 128 256), losses := [] }

theorem u26427 : Upper (D 6) (R 6) [40,129,258,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26427 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26428 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 262 76 82 33 116 180 308), lower := (rows 41 131 262 76 82 33 64 128 256), losses := [] }

theorem u26428 : Upper (D 6) (R 6) [40,129,258,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26429 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 262 76 82 36 113 177 305), lower := (rows 41 131 262 76 82 36 64 128 256), losses := [] }

theorem u26429 : Upper (D 6) (R 6) [40,129,258,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26430 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 41 131 262 76 82 48 101 165 293), lower := (rows 41 131 262 76 82 48 64 128 256), losses := [] }

theorem u26430 : Upper (D 6) (R 6) [40,129,258,68,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26430 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26431 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 131 262 76 112 33 86 150 278), lower := (rows 41 131 262 76 112 33 64 128 256), losses := [] }

theorem u26431 : Upper (D 6) (R 6) [40,129,258,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26432 : PairBound 9 := { available := 21, camps := [], pairs := [(0,2),(4,0),(4,2)], upper := (rows 41 131 262 76 112 34 85 149 277), lower := (rows 41 131 262 76 112 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 38 64 128 256), good := (rows 56 162 294 124 112 34 64 128 256) },{ target := 2, region := (rows 9 2 0 8 24 38 64 128 256), good := (rows 57 163 290 121 112 34 64 128 256) }] }

theorem u26432 : Upper (D 6) (R 6) [40,129,258,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26433 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 262 76 112 36 83 147 275), lower := (rows 41 131 262 76 112 36 64 128 256), losses := [] }

theorem u26433 : Upper (D 6) (R 6) [40,129,258,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26434 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2)], upper := (rows 41 131 262 76 112 48 71 135 263), lower := (rows 41 131 262 76 112 48 64 128 256), losses := [] }

theorem u26434 : Upper (D 6) (R 6) [40,129,258,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26434 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26435 : Route 9 := (fun mask => (mask,id))

def c26435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26435 : Upper (D 6) (R 6) [40,129,258,80,5,2] 13 := by
  apply FastRouting.sound _ _ [40,129,258,80,5,2] 13 (by decide) (choices 1) [4,32] r26435 c26435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8235
  · exact u8236

def b26436 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 194, targets := 4 },{ cop := 1, region := 356, targets := 1 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 41 131 262 88 21 36 98 226 354), lower := (rows 41 131 262 88 21 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 24 16 54 70 134 262), good := (rows 40 486 486 120 508 484 64 128 256) }] }

theorem u26436 : Upper (D 6) (R 6) [40,129,258,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26437 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 262 88 21 96 102 166 294), lower := (rows 41 131 262 88 21 96 64 128 256), losses := [] }

theorem u26437 : Upper (D 6) (R 6) [40,129,258,80,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26438 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 262 88 52 33 70 198 326), lower := (rows 41 131 262 88 52 33 64 128 256), losses := [] }

theorem u26438 : Upper (D 6) (R 6) [40,129,258,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26439 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(4,0)], upper := (rows 41 131 262 88 52 34 69 197 325), lower := (rows 41 131 262 88 52 34 64 128 256), losses := [] }

theorem u26439 : Upper (D 6) (R 6) [40,129,258,80,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26440 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 41 131 262 88 52 36 67 195 323), lower := (rows 41 131 262 88 52 36 64 128 256), losses := [] }

theorem u26440 : Upper (D 6) (R 6) [40,129,258,80,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26441 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 131 262 88 52 96 71 135 263), lower := (rows 41 131 262 88 52 96 64 128 256), losses := [] }

theorem u26441 : Upper (D 6) (R 6) [40,129,258,80,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26442 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(0,6),(2,0),(4,0)], upper := (rows 41 131 276 13 82 34 100 228 356), lower := (rows 41 131 276 13 82 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 12 16 50 0 128 256), good := (rows 41 163 317 13 50 34 0 128 256) }] }

theorem u26442 : Upper (D 6) (R 6) [40,129,272,5,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26443 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 131 276 13 82 36 98 226 354), lower := (rows 41 131 276 13 82 36 64 128 256), losses := [] }

theorem u26443 : Upper (D 6) (R 6) [40,129,272,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26444 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 372, targets := 1 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 41 131 276 13 82 96 102 166 294), lower := (rows 41 131 276 13 82 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 16 112 64 128 256), good := (rows 41 129 317 13 112 96 96 128 256) }] }

theorem u26444 : Upper (D 6) (R 6) [40,129,272,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26445 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 276 14 21 34 96 224 352), lower := (rows 41 131 276 14 21 34 64 128 256), losses := [] }

theorem u26445 : Upper (D 6) (R 6) [40,129,272,6,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26446 : Route 9 := (fun mask => (mask,id))

def c26446 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26446 : Upper (D 6) (R 6) [40,129,272,6,5,64] 13 := by
  apply FastRouting.sound _ _ [40,129,272,6,5,64] 13 (by decide) (choices 1) [2,32] r26446 c26446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8237
  · exact u8238

def b26447 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 131 276 14 50 33 68 196 324), lower := (rows 41 131 276 14 50 33 64 128 256), losses := [] }

theorem u26447 : Upper (D 6) (R 6) [40,129,272,6,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26448 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 41 131 276 14 50 36 65 193 321), lower := (rows 41 131 276 14 50 36 64 128 256), losses := [] }

theorem u26448 : Upper (D 6) (R 6) [40,129,272,6,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26449 : Route 9 := (fun mask => (mask,id))

def c26449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26449 : Upper (D 6) (R 6) [40,129,272,6,34,64] 13 := by
  apply FastRouting.sound _ _ [40,129,272,6,34,64] 13 (by decide) (choices 1) [1,4] r26449 c26449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8239
  · exact u8240

def b26450 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 276 14 81 34 100 228 356), lower := (rows 41 131 276 14 81 34 64 128 256), losses := [] }

theorem u26450 : Upper (D 6) (R 6) [40,129,272,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26451 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 276 14 81 36 98 226 354), lower := (rows 41 131 276 14 81 36 64 128 256), losses := [] }

theorem u26451 : Upper (D 6) (R 6) [40,129,272,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26452 : Route 9 := (fun mask => (mask,id))

def c26452 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26452 : Upper (D 6) (R 6) [40,129,272,6,65,64] 13 := by
  apply FastRouting.sound _ _ [40,129,272,6,65,64] 13 (by decide) (choices 1) [2,4,32] r26452 c26452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8241
  · exact u8242
  · exact u8243

def b26453 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 33, targets := 68 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 276 14 82 33 100 228 356), lower := (rows 41 131 276 14 82 33 64 128 256), losses := [] }

theorem u26453 : Upper (D 6) (R 6) [40,129,272,6,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26454 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 210, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 131 276 14 82 36 97 225 353), lower := (rows 41 131 276 14 82 36 64 128 256), losses := [] }

theorem u26454 : Upper (D 6) (R 6) [40,129,272,6,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26455 : Route 9 := (fun mask => (mask,id))

def c26455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26455 : Upper (D 6) (R 6) [40,129,272,6,66,64] 13 := by
  apply FastRouting.sound _ _ [40,129,272,6,66,64] 13 (by decide) (choices 1) [1,4,32] r26455 c26455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8244
  · exact u8245
  · exact u8246

def b26456 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 276 14 84 33 98 226 354), lower := (rows 41 131 276 14 84 33 64 128 256), losses := [] }

theorem u26456 : Upper (D 6) (R 6) [40,129,272,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26457 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 131 276 14 84 34 97 225 353), lower := (rows 41 131 276 14 84 34 64 128 256), losses := [] }

theorem u26457 : Upper (D 6) (R 6) [40,129,272,6,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26458 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 0, region := 130, targets := 64 }], pairs := [(0,2),(1,2),(1,6)], upper := (rows 41 131 276 14 84 96 99 163 291), lower := (rows 41 131 276 14 84 96 64 128 256), losses := [] }

theorem u26458 : Upper (D 6) (R 6) [40,129,272,6,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26459 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 131 276 14 112 33 70 198 326), lower := (rows 41 131 276 14 112 33 64 128 256), losses := [] }

theorem u26459 : Upper (D 6) (R 6) [40,129,272,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u26459
end Delivery.IrregularNine14.P06
