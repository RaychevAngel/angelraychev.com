import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0320
import IrregularNine14P06C0321

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35460 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 134 292 11 22 97 97 225 353), lower := (rows 25 134 292 11 22 32 64 128 256), losses := [] }

theorem u35460 : Upper (D 6) (R 6) [24,132,288,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35461 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 25 134 292 11 49 102 70 198 326), lower := (rows 25 134 292 11 49 32 64 128 256), losses := [] }

theorem u35461 : Upper (D 6) (R 6) [24,132,288,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35462 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 134 292 11 50 101 69 197 325), lower := (rows 25 134 292 11 50 32 64 128 256), losses := [] }

theorem u35462 : Upper (D 6) (R 6) [24,132,288,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35463 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 25 134 292 11 52 99 67 195 323), lower := (rows 25 134 292 11 52 32 64 128 256), losses := [] }

theorem u35463 : Upper (D 6) (R 6) [24,132,288,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35464 : Route 9 := (fun mask => (mask,id))

def c35464 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35464 : Upper (D 6) (R 6) [24,132,288,3,65] 13 := by
  apply FastRouting.sound _ _ [24,132,288,3,65] 13 (by decide) (choices 1) [2,4,64] r35464 c35464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19220
  · exact u19221
  · exact u19222

def b35465 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 134 292 11 82 101 101 229 357), lower := (rows 25 134 292 11 82 32 64 128 256), losses := [] }

theorem u35465 : Upper (D 6) (R 6) [24,132,288,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35466 : Route 9 := (fun mask => (mask,id))

def c35466 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35466 : Upper (D 6) (R 6) [24,132,288,3,68] 13 := by
  apply FastRouting.sound _ _ [24,132,288,3,68] 13 (by decide) (choices 1) [1,2,64] r35466 c35466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19223
  · exact u19224
  · exact u19225

def r35467 : Route 9 := (fun mask => (mask,id))

def c35467 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35467 : Upper (D 6) (R 6) [24,132,288,3,96] 13 := by
  apply FastRouting.sound _ _ [24,132,288,3,96] 13 (by decide) (choices 1) [1,2,4,64] r35467 c35467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19226
  · exact u19227
  · exact u19228
  · exact u19229

def b35468 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 25, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 25 134 292 13 49 98 66 194 322), lower := (rows 25 134 292 13 49 32 64 128 256), losses := [] }

theorem u35468 : Upper (D 6) (R 6) [24,132,288,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35469 : Route 9 := (fun mask => (mask,id))

def c35469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35469 : Upper (D 6) (R 6) [24,132,288,5,34] 13 := by
  apply FastRouting.sound _ _ [24,132,288,5,34] 13 (by decide) (choices 1) [1,2,64] r35469 c35469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19230
  · exact u19231
  · exact u19232

def r35470 : Route 9 := (fun mask => (mask,id))

def c35470 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35470 : Upper (D 6) (R 6) [24,132,288,5,65] 13 := by
  apply FastRouting.sound _ _ [24,132,288,5,65] 13 (by decide) (choices 1) [2,64] r35470 c35470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19233
  · exact u19234

def r35471 : Route 9 := (fun mask => (mask,id))

def c35471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35471 : Upper (D 6) (R 6) [24,132,288,5,66] 13 := by
  apply FastRouting.sound _ _ [24,132,288,5,66] 13 (by decide) (choices 1) [1,2,64] r35471 c35471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19235
  · exact u19236
  · exact u19237

def r35472 : Route 9 := (fun mask => (mask,id))

def c35472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35472 : Upper (D 6) (R 6) [24,132,288,5,96] 13 := by
  apply FastRouting.sound _ _ [24,132,288,5,96] 13 (by decide) (choices 1) [1,2,64] r35472 c35472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19238
  · exact u19239
  · exact u19240

def b35473 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 134 292 14 49 99 67 195 323), lower := (rows 25 134 292 14 49 32 64 128 256), losses := [] }

theorem u35473 : Upper (D 6) (R 6) [24,132,288,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35474 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 134 292 14 50 97 65 193 321), lower := (rows 25 134 292 14 50 32 64 128 256), losses := [] }

theorem u35474 : Upper (D 6) (R 6) [24,132,288,6,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35475 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 134 292 14 81 99 99 227 355), lower := (rows 25 134 292 14 81 32 64 128 256), losses := [] }

theorem u35475 : Upper (D 6) (R 6) [24,132,288,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35476 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 134 292 14 82 97 97 225 353), lower := (rows 25 134 292 14 82 32 64 128 256), losses := [] }

theorem u35476 : Upper (D 6) (R 6) [24,132,288,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35477 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 134 292 14 112 99 67 195 323), lower := (rows 25 134 292 14 112 32 64 128 256), losses := [] }

theorem u35477 : Upper (D 6) (R 6) [24,132,288,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35478 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 25 134 292 41 81 102 70 198 326), lower := (rows 25 134 292 41 81 32 64 128 256), losses := [] }

theorem u35478 : Upper (D 6) (R 6) [24,132,288,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35479 : Route 9 := (fun mask => (mask,id))

def c35479 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35479 : Upper (D 6) (R 6) [24,132,288,33,66] 13 := by
  apply FastRouting.sound _ _ [24,132,288,33,66] 13 (by decide) (choices 1) [1,2,4,64] r35479 c35479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19241
  · exact u19242
  · exact u19243
  · exact u19244

def r35480 : Route 9 := (fun mask => (mask,id))

def c35480 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35480 : Upper (D 6) (R 6) [24,132,288,33,68] 13 := by
  apply FastRouting.sound _ _ [24,132,288,33,68] 13 (by decide) (choices 1) [1,2,64] r35480 c35480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19245
  · exact u19246
  · exact u19247

def r35481 : Route 9 := (fun mask => (mask,id))

def c35481 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35481 : Upper (D 6) (R 6) [24,132,288,34,65] 13 := by
  apply FastRouting.sound _ _ [24,132,288,34,65] 13 (by decide) (choices 1) [1,2,4,64] r35481 c35481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19248
  · exact u19249
  · exact u19250
  · exact u19251

def r35482 : Route 9 := (fun mask => (mask,id))

def c35482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35482 : Upper (D 6) (R 6) [24,132,288,34,66] 13 := by
  apply FastRouting.sound _ _ [24,132,288,34,66] 13 (by decide) (choices 1) [1,4,64] r35482 c35482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19252
  · exact u19253
  · exact u19254

def r35483 : Route 9 := (fun mask => (mask,id))

def c35483 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35483 : Upper (D 6) (R 6) [24,132,288,34,68] 13 := by
  apply FastRouting.sound _ _ [24,132,288,34,68] 13 (by decide) (choices 1) [1,2,64] r35483 c35483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19255
  · exact u19256
  · exact u19257

def b35484 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 134 292 44 81 99 67 195 323), lower := (rows 25 134 292 44 81 32 64 128 256), losses := [] }

theorem u35484 : Upper (D 6) (R 6) [24,132,288,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35485 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 134 292 44 82 99 67 195 323), lower := (rows 25 134 292 44 82 32 64 128 256), losses := [] }

theorem u35485 : Upper (D 6) (R 6) [24,132,288,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35486 : PairBound 9 := { available := 38, camps := [{ cop := 6, region := 25, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 134 292 73 81 38 102 166 294), lower := (rows 25 134 292 73 81 32 64 128 256), losses := [] }

theorem u35486 : Upper (D 6) (R 6) [24,132,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35487 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 134 292 73 82 39 103 167 295), lower := (rows 25 134 292 73 82 32 64 128 256), losses := [] }

theorem u35487 : Upper (D 6) (R 6) [24,132,288,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35488 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 134 292 73 84 35 99 163 291), lower := (rows 25 134 292 73 84 32 64 128 256), losses := [] }

theorem u35488 : Upper (D 6) (R 6) [24,132,288,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35489 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 134 292 73 112 39 71 135 263), lower := (rows 25 134 292 73 112 32 64 128 256), losses := [] }

theorem u35489 : Upper (D 6) (R 6) [24,132,288,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35490 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 134 292 74 82 37 101 165 293), lower := (rows 25 134 292 74 82 32 64 128 256), losses := [] }

theorem u35490 : Upper (D 6) (R 6) [24,132,288,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35491 : Route 9 := (fun mask => (mask,id))

def c35491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35491 : Upper (D 6) (R 6) [24,132,288,66,68] 13 := by
  apply FastRouting.sound _ _ [24,132,288,66,68] 13 (by decide) (choices 1) [1,2] r35491 c35491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19258
  · exact u19259

def r35492 : Route 9 := (fun mask => (mask,id))

def c35492 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35492 : Upper (D 6) (R 6) [24,132,288,66,96] 13 := by
  apply FastRouting.sound _ _ [24,132,288,66,96] 13 (by decide) (choices 1) [1,2,4] r35492 c35492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19260
  · exact u19261
  · exact u19262

def r35493 : Route 9 := (fun mask => (mask,id))

def c35493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35493 : Upper (D 6) (R 6) [24,132,288,68,96] 13 := by
  apply FastRouting.sound _ _ [24,132,288,68,96] 13 (by decide) (choices 1) [1,2] r35493 c35493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19263
  · exact u19264

def b35494 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 162 292 11 19 100 68 196 324), lower := (rows 25 162 292 11 19 32 64 128 256), losses := [] }

theorem u35494 : Upper (D 6) (R 6) [24,160,288,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m35495_4 : Upper (D 6) (R 6) [24,160,288,3,5,4] 13 :=
  permutation_upper _ _ _ [24,160,288,3,5,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19265

def r35495 : Route 9 := (fun mask => (mask,id))

def c35495 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35495 : Upper (D 6) (R 6) [24,160,288,3,5] 13 := by
  apply FastRouting.sound _ _ [24,160,288,3,5] 13 (by decide) (choices 1) [2,4,64] r35495 c35495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19265
  · exact m35495_4
  · exact u19266

def b35496 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 162 292 11 22 101 69 197 325), lower := (rows 25 162 292 11 22 32 64 128 256), losses := [] }

theorem u35496 : Upper (D 6) (R 6) [24,160,288,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35497 : Route 9 := (fun mask => (mask,id))

def c35497 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35497 : Upper (D 6) (R 6) [24,160,288,3,65] 13 := by
  apply FastRouting.sound _ _ [24,160,288,3,65] 13 (by decide) (choices 1) [2,4,64] r35497 c35497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19267
  · exact u19268
  · exact u19269

def b35498 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 162 292 11 82 101 69 197 325), lower := (rows 25 162 292 11 82 32 64 128 256), losses := [] }

theorem u35498 : Upper (D 6) (R 6) [24,160,288,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35499 : Route 9 := (fun mask => (mask,id))

def c35499 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35499 : Upper (D 6) (R 6) [24,160,288,3,68] 13 := by
  apply FastRouting.sound _ _ [24,160,288,3,68] 13 (by decide) (choices 1) [1,2,4,64] r35499 c35499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19270
  · exact u19271
  · exact u19272
  · exact u19273

def b35500 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 17, targets := 32 },{ cop := 3, region := 17, targets := 64 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 162 292 14 22 97 65 193 321), lower := (rows 25 162 292 14 22 32 64 128 256), losses := [] }

theorem u35500 : Upper (D 6) (R 6) [24,160,288,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m35501_4 : Upper (D 6) (R 6) [24,160,288,6,65,4] 13 :=
  permutation_upper _ _ _ [24,160,288,6,65,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19275

def r35501 : Route 9 := (fun mask => (mask,id))

def c35501 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35501 : Upper (D 6) (R 6) [24,160,288,6,65] 13 := by
  apply FastRouting.sound _ _ [24,160,288,6,65] 13 (by decide) (choices 1) [1,2,4,64] r35501 c35501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19274
  · exact u19275
  · exact m35501_4
  · exact u19276

def b35502 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 81, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(2,1),(4,5)], upper := (rows 25 162 292 14 82 101 69 197 325), lower := (rows 25 162 292 14 82 32 64 128 256), losses := [] }

theorem u35502 : Upper (D 6) (R 6) [24,160,288,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35503 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 25, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 162 292 73 81 38 70 134 262), lower := (rows 25 162 292 73 81 32 64 128 256), losses := [] }

theorem u35503 : Upper (D 6) (R 6) [24,160,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35504 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 162 292 73 82 39 71 135 263), lower := (rows 25 162 292 73 82 32 64 128 256), losses := [] }

theorem u35504 : Upper (D 6) (R 6) [24,160,288,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35505 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 162 292 74 82 37 69 133 261), lower := (rows 25 162 292 74 82 32 64 128 256), losses := [] }

theorem u35505 : Upper (D 6) (R 6) [24,160,288,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m35506_4 : Upper (D 6) (R 6) [24,160,288,66,68,4] 13 :=
  permutation_upper _ _ _ [24,160,288,66,68,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19278

def r35506 : Route 9 := (fun mask => (mask,id))

def c35506 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35506 : Upper (D 6) (R 6) [24,160,288,66,68] 13 := by
  apply FastRouting.sound _ _ [24,160,288,66,68] 13 (by decide) (choices 1) [1,2,4] r35506 c35506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19277
  · exact u19278
  · exact m35506_4

def b35507 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 162 324 11 19 100 100 228 356), lower := (rows 25 162 324 11 19 32 64 128 256), losses := [] }

theorem u35507 : Upper (D 6) (R 6) [24,160,320,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35508 : Route 9 := (fun mask => (mask,id))

def c35508 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35508 : Upper (D 6) (R 6) [24,160,320,3,5] 13 := by
  apply FastRouting.sound _ _ [24,160,320,3,5] 13 (by decide) (choices 1) [2,4,64] r35508 c35508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19279
  · exact u19280
  · exact u19281

def b35509 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 162 324 11 22 101 101 229 357), lower := (rows 25 162 324 11 22 32 64 128 256), losses := [] }

theorem u35509 : Upper (D 6) (R 6) [24,160,320,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35510 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 162 324 11 49 102 70 198 326), lower := (rows 25 162 324 11 49 32 64 128 256), losses := [] }

theorem u35510 : Upper (D 6) (R 6) [24,160,320,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35511 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 162 324 11 50 101 69 197 325), lower := (rows 25 162 324 11 50 32 64 128 256), losses := [] }

theorem u35511 : Upper (D 6) (R 6) [24,160,320,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35512 : Route 9 := (fun mask => (mask,id))

def c35512 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35512 : Upper (D 6) (R 6) [24,160,320,3,36] 13 := by
  apply FastRouting.sound _ _ [24,160,320,3,36] 13 (by decide) (choices 1) [1,2,4,64] r35512 c35512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19282
  · exact u19283
  · exact u19284
  · exact u19285

def b35513 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 2, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 162 324 11 81 38 102 166 294), lower := (rows 25 162 324 11 81 32 64 128 256), losses := [] }

theorem u35513 : Upper (D 6) (R 6) [24,160,320,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35514 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 162 324 11 82 37 101 165 293), lower := (rows 25 162 324 11 82 32 64 128 256), losses := [] }

theorem u35514 : Upper (D 6) (R 6) [24,160,320,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35515 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 162 324 11 84 39 103 167 295), lower := (rows 25 162 324 11 84 32 64 128 256), losses := [] }

theorem u35515 : Upper (D 6) (R 6) [24,160,320,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35516 : Route 9 := (fun mask => (mask,id))

def c35516 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35516 : Upper (D 6) (R 6) [24,160,320,3,96] 13 := by
  apply FastRouting.sound _ _ [24,160,320,3,96] 13 (by decide) (choices 1) [1,2,4] r35516 c35516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19286
  · exact u19287
  · exact u19288

def b35517 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 17, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 162 324 14 22 97 97 225 353), lower := (rows 25 162 324 14 22 32 64 128 256), losses := [] }

theorem u35517 : Upper (D 6) (R 6) [24,160,320,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35518 : Route 9 := (fun mask => (mask,id))

def c35518 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35518 : Upper (D 6) (R 6) [24,160,320,6,33] 13 := by
  apply FastRouting.sound _ _ [24,160,320,6,33] 13 (by decide) (choices 1) [1,2,4,64] r35518 c35518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19289
  · exact u19290
  · exact u19291
  · exact u19292

def b35519 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 162 324 14 50 101 69 197 325), lower := (rows 25 162 324 14 50 32 64 128 256), losses := [] }

theorem u35519 : Upper (D 6) (R 6) [24,160,320,6,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u35519
end Delivery.IrregularNine14.P06
