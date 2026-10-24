import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0158

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26400 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 266 69 200 50 34 209 145 401), lower := (rows 37 266 69 200 50 34 64 128 256), losses := [] }

theorem u26400 : Upper (D 7) (R 7) [36,264,65,192,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26401 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 69 200 50 48 195 131 387), lower := (rows 37 266 69 200 50 48 64 128 256), losses := [] }

theorem u26401 : Upper (D 7) (R 7) [36,264,65,192,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26401 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26402 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 37, targets := 2 },{ cop := 4, region := 69, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 200 50 160 83 147 275), lower := (rows 37 266 69 200 50 160 64 128 256), losses := [] }

theorem u26402 : Upper (D 7) (R 7) [36,264,65,192,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26403 : Route 9 := (fun mask => (mask,id))

def c26403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26403 : Upper (D 7) (R 7) [36,264,65,192,129,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,192,129,2] 13 (by decide) (choices 1) [2,16,32] r26403 c26403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9485
  · exact u9486
  · exact u9487

def b26404 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 53, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 266 69 200 145 48 98 162 290), lower := (rows 37 266 69 200 145 48 64 128 256), losses := [] }

theorem u26404 : Upper (D 7) (R 7) [36,264,65,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26404 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26405 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 266 69 200 146 33 114 178 306), lower := (rows 37 266 69 200 146 33 64 128 256), losses := [] }

theorem u26405 : Upper (D 7) (R 7) [36,264,65,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26406 : Route 9 := (fun mask => (mask,id))

def c26406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26406 : Upper (D 7) (R 7) [36,264,65,192,130,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,192,130,2] 13 (by decide) (choices 1) [1,16,32] r26406 c26406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9488
  · exact u9489
  · exact u9490

def r26407 : Route 9 := (fun mask => (mask,id))

def c26407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26407 : Upper (D 7) (R 7) [36,264,65,192,130,16] 13 := by
  apply FastRouting.sound _ _ [36,264,65,192,130,16] 13 (by decide) (choices 1) [1,2,32] r26407 c26407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9491
  · exact u9492
  · exact u9493

def b26408 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 266 69 200 176 33 82 146 274), lower := (rows 37 266 69 200 176 33 64 128 256), losses := [] }

theorem u26408 : Upper (D 7) (R 7) [36,264,65,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26409 : Route 9 := (fun mask => (mask,id))

def c26409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26409 : Upper (D 7) (R 7) [36,264,65,192,160,2] 13 := by
  apply FastRouting.sound _ _ [36,264,65,192,160,2] 13 (by decide) (choices 1) [1,2,16] r26409 c26409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9494
  · exact u9495
  · exact u9496

def b26410 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 69 200 176 48 67 131 259), lower := (rows 37 266 69 200 176 48 64 128 256), losses := [] }

theorem u26410 : Upper (D 7) (R 7) [36,264,65,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26410 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26411 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 57, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,7)], upper := (rows 37 266 70 11 112 33 208 144 400), lower := (rows 37 266 70 11 112 33 64 128 256), losses := [] }

theorem u26411 : Upper (D 7) (R 7) [36,264,66,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26412 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 70 11 112 48 193 129 385), lower := (rows 37 266 70 11 112 48 64 128 256), losses := [] }

theorem u26412 : Upper (D 7) (R 7) [36,264,66,3,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26412 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26413 : Route 9 := (fun mask => (mask,id))

def c26413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26413 : Upper (D 7) (R 7) [36,264,66,3,96,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,3,96,128] 13 (by decide) (choices 1) [1,16,128] r26413 c26413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9497
  · exact u9498
  · exact u9499

def b26414 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(1,0),(4,1)], upper := (rows 37 266 70 11 145 48 224 224 480), lower := (rows 37 266 70 11 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 48 113 177 305), good := (rows 484 270 70 462 496 496 64 128 256) }] }

theorem u26414 : Upper (D 7) (R 7) [36,264,66,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26414 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26415 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 11 145 96 240 176 432), lower := (rows 37 266 70 11 145 96 64 128 256), losses := [] }

theorem u26415 : Upper (D 7) (R 7) [36,264,66,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26416 : Route 9 := (fun mask => (mask,id))

def c26416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26416 : Upper (D 7) (R 7) [36,264,66,3,129,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,3,129,128] 13 (by decide) (choices 1) [16,32] r26416 c26416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9500
  · exact u9501

def b26417 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 266 70 11 176 33 208 208 464), lower := (rows 37 266 70 11 176 33 64 128 256), losses := [] }

theorem u26417 : Upper (D 7) (R 7) [36,264,66,3,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26418 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 266 70 11 176 48 193 193 449), lower := (rows 37 266 70 11 176 48 64 128 256), losses := [] }

theorem u26418 : Upper (D 7) (R 7) [36,264,66,3,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26418 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26419 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 11 176 96 209 145 401), lower := (rows 37 266 70 11 176 96 64 128 256), losses := [] }

theorem u26419 : Upper (D 7) (R 7) [36,264,66,3,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26420 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 70 11 176 160 81 209 337), lower := (rows 37 266 70 11 176 160 64 128 256), losses := [] }

theorem u26420 : Upper (D 7) (R 7) [36,264,66,3,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26421 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 266 70 11 208 33 240 176 432), lower := (rows 37 266 70 11 208 33 64 128 256), losses := [] }

theorem u26421 : Upper (D 7) (R 7) [36,264,66,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26422 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(1,6),(3,6)], upper := (rows 37 266 70 11 208 48 225 161 417), lower := (rows 37 266 70 11 208 48 64 128 256), losses := [] }

theorem u26422 : Upper (D 7) (R 7) [36,264,66,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26422 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26423 : Route 9 := (fun mask => (mask,id))

def c26423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26423 : Upper (D 7) (R 7) [36,264,66,3,192,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,3,192,128] 13 (by decide) (choices 1) [1,16,32] r26423 c26423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9502
  · exact u9503
  · exact u9504

def b26424 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 266 70 25 50 33 192 192 448), lower := (rows 37 266 70 25 50 33 64 128 256), losses := [] }

theorem u26424 : Upper (D 7) (R 7) [36,264,66,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26425 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 25 50 96 193 129 385), lower := (rows 37 266 70 25 50 96 64 128 256), losses := [] }

theorem u26425 : Upper (D 7) (R 7) [36,264,66,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26426 : Route 9 := (fun mask => (mask,id))

def c26426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26426 : Upper (D 7) (R 7) [36,264,66,17,34,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,17,34,128] 13 (by decide) (choices 1) [1,128] r26426 c26426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9505
  · exact u9506

def b26427 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 266 70 25 146 33 224 224 480), lower := (rows 37 266 70 25 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 24 32 97 161 289), good := (rows 484 286 70 478 146 480 64 128 256) }] }

theorem u26427 : Upper (D 7) (R 7) [36,264,66,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26428 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 25 146 96 225 161 417), lower := (rows 37 266 70 25 146 96 64 128 256), losses := [] }

theorem u26428 : Upper (D 7) (R 7) [36,264,66,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26428 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26429 : Route 9 := (fun mask => (mask,id))

def c26429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26429 : Upper (D 7) (R 7) [36,264,66,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,17,130,128] 13 (by decide) (choices 1) [1,32] r26429 c26429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9507
  · exact u9508

def b26430 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 266 70 25 176 33 194 194 450), lower := (rows 37 266 70 25 176 33 64 128 256), losses := [] }

theorem u26430 : Upper (D 7) (R 7) [36,264,66,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26431 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 266 70 25 176 34 193 193 449), lower := (rows 37 266 70 25 176 34 64 128 256), losses := [] }

theorem u26431 : Upper (D 7) (R 7) [36,264,66,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26432 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 25 176 96 195 131 387), lower := (rows 37 266 70 25 176 96 64 128 256), losses := [] }

theorem u26432 : Upper (D 7) (R 7) [36,264,66,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26433 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 70 25 176 160 67 195 323), lower := (rows 37 266 70 25 176 160 64 128 256), losses := [] }

theorem u26433 : Upper (D 7) (R 7) [36,264,66,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26434 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 33, targets := 64 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 266 70 25 208 33 226 162 418), lower := (rows 37 266 70 25 208 33 64 128 256), losses := [] }

theorem u26434 : Upper (D 7) (R 7) [36,264,66,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26434 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26435 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 266 70 25 208 34 225 161 417), lower := (rows 37 266 70 25 208 34 64 128 256), losses := [] }

theorem u26435 : Upper (D 7) (R 7) [36,264,66,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26436 : Route 9 := (fun mask => (mask,id))

def c26436 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26436 : Upper (D 7) (R 7) [36,264,66,17,192,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,17,192,128] 13 (by decide) (choices 1) [1,2,32] r26436 c26436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9509
  · exact u9510
  · exact u9511

def b26437 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 57, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,7)], upper := (rows 37 266 70 26 112 33 193 129 385), lower := (rows 37 266 70 26 112 33 64 128 256), losses := [] }

theorem u26437 : Upper (D 7) (R 7) [36,264,66,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26438 : Route 9 := (fun mask => (mask,id))

def c26438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26438 : Upper (D 7) (R 7) [36,264,66,18,96,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,18,96,128] 13 (by decide) (choices 1) [1,128] r26438 c26438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9512
  · exact u9513

def b26439 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 266 70 26 145 33 224 224 480), lower := (rows 37 266 70 26 145 33 64 128 256), losses := [] }

theorem u26439 : Upper (D 7) (R 7) [36,264,66,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26440 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 26 145 96 225 161 417), lower := (rows 37 266 70 26 145 96 64 128 256), losses := [] }

theorem u26440 : Upper (D 7) (R 7) [36,264,66,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26441 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(1,7),(2,7),(4,1)], upper := (rows 37 266 70 26 145 160 97 225 353), lower := (rows 37 266 70 26 145 160 64 128 256), losses := [{ target := 7, region := (rows 1 18 20 24 16 32 65 0 257), good := (rows 357 266 70 30 351 32 64 0 256) }] }

theorem u26441 : Upper (D 7) (R 7) [36,264,66,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26442 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 266 70 26 176 33 193 193 449), lower := (rows 37 266 70 26 176 33 64 128 256), losses := [] }

theorem u26442 : Upper (D 7) (R 7) [36,264,66,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26443 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 26 176 96 193 129 385), lower := (rows 37 266 70 26 176 96 64 128 256), losses := [] }

theorem u26443 : Upper (D 7) (R 7) [36,264,66,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26444 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 266 70 26 176 160 65 193 321), lower := (rows 37 266 70 26 176 160 64 128 256), losses := [] }

theorem u26444 : Upper (D 7) (R 7) [36,264,66,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26445 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 266 70 26 208 33 225 161 417), lower := (rows 37 266 70 26 208 33 64 128 256), losses := [] }

theorem u26445 : Upper (D 7) (R 7) [36,264,66,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26446 : Route 9 := (fun mask => (mask,id))

def c26446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26446 : Upper (D 7) (R 7) [36,264,66,18,192,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,18,192,128] 13 (by decide) (choices 1) [1,32] r26446 c26446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9514
  · exact u9515

def b26447 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 266 70 42 145 33 208 208 464), lower := (rows 37 266 70 42 145 33 64 128 256), losses := [] }

theorem u26447 : Upper (D 7) (R 7) [36,264,66,34,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26448 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 177, targets := 2 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,1),(4,1),(4,5)], upper := (rows 37 266 70 42 145 48 193 193 449), lower := (rows 37 266 70 42 145 48 64 128 256), losses := [] }

theorem u26448 : Upper (D 7) (R 7) [36,264,66,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26448 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26449 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 42 145 96 209 145 401), lower := (rows 37 266 70 42 145 96 64 128 256), losses := [] }

theorem u26449 : Upper (D 7) (R 7) [36,264,66,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26450 : Route 9 := (fun mask => (mask,id))

def c26450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26450 : Upper (D 7) (R 7) [36,264,66,34,129,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,34,129,128] 13 (by decide) (choices 1) [1,16] r26450 c26450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9516
  · exact u9517

def b26451 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 266 70 42 208 33 209 145 401), lower := (rows 37 266 70 42 208 33 64 128 256), losses := [] }

theorem u26451 : Upper (D 7) (R 7) [36,264,66,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26452 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1),(1,6),(3,6)], upper := (rows 37 266 70 42 208 48 193 129 385), lower := (rows 37 266 70 42 208 48 64 128 256), losses := [] }

theorem u26452 : Upper (D 7) (R 7) [36,264,66,34,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26452 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26453 : Route 9 := (fun mask => (mask,id))

def c26453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26453 : Upper (D 7) (R 7) [36,264,66,34,192,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,34,192,128] 13 (by decide) (choices 1) [1,16] r26453 c26453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u9518
  · exact u9519

def b26454 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 57, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 37 266 70 56 81 33 194 130 386), lower := (rows 37 266 70 56 81 33 64 128 256), losses := [] }

theorem u26454 : Upper (D 7) (R 7) [36,264,66,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26455 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 57, targets := 128 },{ cop := 0, region := 216, targets := 2 }], pairs := [(0,7),(3,1),(3,7),(4,7)], upper := (rows 37 266 70 56 81 34 193 129 385), lower := (rows 37 266 70 56 81 34 64 128 256), losses := [] }

theorem u26455 : Upper (D 7) (R 7) [36,264,66,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26456 : Route 9 := (fun mask => (mask,id))

def c26456 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26456 : Upper (D 7) (R 7) [36,264,66,48,65,128] 13 := by
  apply FastRouting.sound _ _ [36,264,66,48,65,128] 13 (by decide) (choices 1) [1,2,128] r26456 c26456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9520
  · exact u9521
  · exact u9522

def b26457 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 266 70 56 145 33 194 194 450), lower := (rows 37 266 70 56 145 33 64 128 256), losses := [] }

theorem u26457 : Upper (D 7) (R 7) [36,264,66,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26458 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 266 70 56 145 34 193 193 449), lower := (rows 37 266 70 56 145 34 64 128 256), losses := [] }

theorem u26458 : Upper (D 7) (R 7) [36,264,66,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26459 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 266 70 56 145 96 195 131 387), lower := (rows 37 266 70 56 145 96 64 128 256), losses := [] }

theorem u26459 : Upper (D 7) (R 7) [36,264,66,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26459
end Delivery.IrregularNine14.P07
