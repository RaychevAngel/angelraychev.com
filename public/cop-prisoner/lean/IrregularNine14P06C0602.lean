import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0340
import IrregularNine14P06C0341

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36120 : Route 9 := (fun mask => (mask,id))

def c36120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36120 : Upper (D 6) (R 6) [34,68,130,96,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,96,257] 13 (by decide) (choices 1) [1,4,8,16] r36120 c36120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20422
  · exact u20423
  · exact u20424
  · exact u20425

def r36121 : Route 9 := (fun mask => (mask,id))

def c36121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36121 : Upper (D 6) (R 6) [34,68,130,96,260] 13 := by
  apply FastRouting.sound _ _ [34,68,130,96,260] 13 (by decide) (choices 1) [1,8,16] r36121 c36121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20426
  · exact u20427
  · exact u20428

def r36122 : Route 9 := (fun mask => (mask,id))

def c36122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36122 : Upper (D 6) (R 6) [34,68,130,96,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,96,264] 13 (by decide) (choices 1) [1,4,16] r36122 c36122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20429
  · exact u20430
  · exact u20431

def b36123 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 1, region := 305, targets := 4 }], pairs := [(0,2),(4,5),(4,6)], upper := (rows 35 70 140 13 19 368 368 496 368), lower := (rows 35 70 140 13 19 32 64 128 256), losses := [] }

theorem u36123 : Upper (D 6) (R 6) [34,68,136,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36124 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 140 13 49 370 338 466 338), lower := (rows 35 70 140 13 49 32 64 128 256), losses := [] }

theorem u36124 : Upper (D 6) (R 6) [34,68,136,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36125 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 35 70 140 13 50 369 337 465 337), lower := (rows 35 70 140 13 50 32 64 128 256), losses := [] }

theorem u36125 : Upper (D 6) (R 6) [34,68,136,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36126 : Route 9 := (fun mask => (mask,id))

def c36126 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36126 : Upper (D 6) (R 6) [34,68,136,5,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,5,65] 13 (by decide) (choices 1) [2,16,256] r36126 c36126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20432
  · exact u20433
  · exact u20434

def b36127 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 140 13 82 305 369 433 305), lower := (rows 35 70 140 13 82 32 64 128 256), losses := [] }

theorem u36127 : Upper (D 6) (R 6) [34,68,136,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36128 : Route 9 := (fun mask => (mask,id))

def c36128 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36128 : Upper (D 6) (R 6) [34,68,136,5,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,5,96] 13 (by decide) (choices 1) [1,2,16,256] r36128 c36128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20435
  · exact u20436
  · exact u20437
  · exact u20438

def r36129 : Route 9 := (fun mask => (mask,id))

def c36129 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36129 : Upper (D 6) (R 6) [34,68,136,5,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,5,257] 13 (by decide) (choices 1) [2,16,64] r36129 c36129
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20439
  · exact u20440
  · exact u20441

def r36130 : Route 9 := (fun mask => (mask,id))

def c36130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36130 : Upper (D 6) (R 6) [34,68,136,5,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,5,258] 13 (by decide) (choices 1) [1,16,64] r36130 c36130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20442
  · exact u20443
  · exact u20444

def r36131 : Route 9 := (fun mask => (mask,id))

def c36131 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36131 : Upper (D 6) (R 6) [34,68,136,5,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,5,288] 13 (by decide) (choices 1) [1,2,16,64] r36131 c36131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20445
  · exact u20446
  · exact u20447
  · exact u20448

def r36132 : Route 9 := (fun mask => (mask,id))

def c36132 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36132 : Upper (D 6) (R 6) [34,68,136,5,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,5,320] 13 (by decide) (choices 1) [1,2,16] r36132 c36132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20449
  · exact u20450
  · exact u20451

def b36133 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 70 140 25 19 356 356 484 356), lower := (rows 35 70 140 25 19 32 64 128 256), losses := [] }

theorem u36133 : Upper (D 6) (R 6) [34,68,136,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36134 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 140 25 21 354 354 482 354), lower := (rows 35 70 140 25 21 32 64 128 256), losses := [] }

theorem u36134 : Upper (D 6) (R 6) [34,68,136,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36134 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36135 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 70 140 25 22 353 353 481 353), lower := (rows 35 70 140 25 22 32 64 128 256), losses := [] }

theorem u36135 : Upper (D 6) (R 6) [34,68,136,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36136 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 70 140 25 49 358 326 454 326), lower := (rows 35 70 140 25 49 32 64 128 256), losses := [] }

theorem u36136 : Upper (D 6) (R 6) [34,68,136,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36136 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36137 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 70 140 25 50 357 325 453 325), lower := (rows 35 70 140 25 50 32 64 128 256), losses := [] }

theorem u36137 : Upper (D 6) (R 6) [34,68,136,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36138 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 70 140 25 52 355 323 451 323), lower := (rows 35 70 140 25 52 32 64 128 256), losses := [] }

theorem u36138 : Upper (D 6) (R 6) [34,68,136,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36139 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 140 25 81 294 358 422 294), lower := (rows 35 70 140 25 81 32 64 128 256), losses := [] }

theorem u36139 : Upper (D 6) (R 6) [34,68,136,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36140 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 140 25 82 293 357 421 293), lower := (rows 35 70 140 25 82 32 64 128 256), losses := [] }

theorem u36140 : Upper (D 6) (R 6) [34,68,136,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36141 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 140 25 84 291 355 419 291), lower := (rows 35 70 140 25 84 32 64 128 256), losses := [] }

theorem u36141 : Upper (D 6) (R 6) [34,68,136,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36142 : PairBound 9 := { available := 263, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(1,5),(2,5)], upper := (rows 35 70 140 25 112 295 327 391 263), lower := (rows 35 70 140 25 112 32 64 128 256), losses := [] }

theorem u36142 : Upper (D 6) (R 6) [34,68,136,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36143 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 70 140 25 273 102 102 230 358), lower := (rows 35 70 140 25 273 32 64 128 256), losses := [] }

theorem u36143 : Upper (D 6) (R 6) [34,68,136,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36144 : Route 9 := (fun mask => (mask,id))

def c36144 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36144 : Upper (D 6) (R 6) [34,68,136,17,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,258] 13 (by decide) (choices 1) [1,4,64] r36144 c36144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20452
  · exact u20453
  · exact u20454

def r36145 : Route 9 := (fun mask => (mask,id))

def c36145 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36145 : Upper (D 6) (R 6) [34,68,136,17,260] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,260] 13 (by decide) (choices 1) [1,2,64] r36145 c36145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20455
  · exact u20456
  · exact u20457

def r36146 : Route 9 := (fun mask => (mask,id))

def c36146 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36146 : Upper (D 6) (R 6) [34,68,136,17,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,288] 13 (by decide) (choices 1) [1,2,4,64] r36146 c36146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20458
  · exact u20459
  · exact u20460
  · exact u20461

def r36147 : Route 9 := (fun mask => (mask,id))

def c36147 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36147 : Upper (D 6) (R 6) [34,68,136,17,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,17,320] 13 (by decide) (choices 1) [1,2,4] r36147 c36147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20462
  · exact u20463
  · exact u20464

def r36148 : Route 9 := (fun mask => (mask,id))

def c36148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36148 : Upper (D 6) (R 6) [34,68,136,18,5] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,5] 13 (by decide) (choices 1) [1,64,256] r36148 c36148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20465
  · exact u20466
  · exact u20467

def b36149 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 70 140 26 49 357 325 453 325), lower := (rows 35 70 140 26 49 32 64 128 256), losses := [] }

theorem u36149 : Upper (D 6) (R 6) [34,68,136,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36150 : Route 9 := (fun mask => (mask,id))

def c36150 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36150 : Upper (D 6) (R 6) [34,68,136,18,36] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,36] 13 (by decide) (choices 1) [1,64,256] r36150 c36150
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20468
  · exact u20469
  · exact u20470

def r36151 : Route 9 := (fun mask => (mask,id))

def c36151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36151 : Upper (D 6) (R 6) [34,68,136,18,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,65] 13 (by decide) (choices 1) [1,4,256] r36151 c36151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20471
  · exact u20472
  · exact u20473

def b36152 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 140 26 84 289 353 417 289), lower := (rows 35 70 140 26 84 32 64 128 256), losses := [] }

theorem u36152 : Upper (D 6) (R 6) [34,68,136,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36153 : Route 9 := (fun mask => (mask,id))

def c36153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36153 : Upper (D 6) (R 6) [34,68,136,18,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,96] 13 (by decide) (choices 1) [1,4,256] r36153 c36153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20474
  · exact u20475
  · exact u20476

def r36154 : Route 9 := (fun mask => (mask,id))

def c36154 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36154 : Upper (D 6) (R 6) [34,68,136,18,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,257] 13 (by decide) (choices 1) [1,4,64] r36154 c36154
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20477
  · exact u20478
  · exact u20479

def r36155 : Route 9 := (fun mask => (mask,id))

def c36155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36155 : Upper (D 6) (R 6) [34,68,136,18,260] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,260] 13 (by decide) (choices 1) [1,64] r36155 c36155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20480
  · exact u20481

def r36156 : Route 9 := (fun mask => (mask,id))

def c36156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36156 : Upper (D 6) (R 6) [34,68,136,18,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,288] 13 (by decide) (choices 1) [1,4,64] r36156 c36156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20482
  · exact u20483
  · exact u20484

def r36157 : Route 9 := (fun mask => (mask,id))

def c36157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36157 : Upper (D 6) (R 6) [34,68,136,18,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,18,320] 13 (by decide) (choices 1) [1,4] r36157 c36157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20485
  · exact u20486

def b36158 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(4,5),(4,6)], upper := (rows 35 70 140 28 19 353 353 481 353), lower := (rows 35 70 140 28 19 32 64 128 256), losses := [] }

theorem u36158 : Upper (D 6) (R 6) [34,68,136,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36159 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 140 28 49 355 323 451 323), lower := (rows 35 70 140 28 49 32 64 128 256), losses := [] }

theorem u36159 : Upper (D 6) (R 6) [34,68,136,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36160 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 35 70 140 28 50 353 321 449 321), lower := (rows 35 70 140 28 50 32 64 128 256), losses := [] }

theorem u36160 : Upper (D 6) (R 6) [34,68,136,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36161 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 28 81 291 355 419 291), lower := (rows 35 70 140 28 81 32 64 128 256), losses := [] }

theorem u36161 : Upper (D 6) (R 6) [34,68,136,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36162 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 24, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 140 28 82 289 353 417 289), lower := (rows 35 70 140 28 82 32 64 128 256), losses := [] }

theorem u36162 : Upper (D 6) (R 6) [34,68,136,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36163 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 28 112 291 323 387 259), lower := (rows 35 70 140 28 112 32 64 128 256), losses := [] }

theorem u36163 : Upper (D 6) (R 6) [34,68,136,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36164 : Route 9 := (fun mask => (mask,id))

def c36164 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36164 : Upper (D 6) (R 6) [34,68,136,20,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,20,257] 13 (by decide) (choices 1) [1,2,64] r36164 c36164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20487
  · exact u20488
  · exact u20489

def r36165 : Route 9 := (fun mask => (mask,id))

def c36165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36165 : Upper (D 6) (R 6) [34,68,136,20,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,20,258] 13 (by decide) (choices 1) [1,64] r36165 c36165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20490
  · exact u20491

def r36166 : Route 9 := (fun mask => (mask,id))

def c36166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36166 : Upper (D 6) (R 6) [34,68,136,20,288] 13 := by
  apply FastRouting.sound _ _ [34,68,136,20,288] 13 (by decide) (choices 1) [1,2,64] r36166 c36166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20492
  · exact u20493
  · exact u20494

def b36167 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 305, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 140 28 336 35 99 163 291), lower := (rows 35 70 140 28 336 32 64 128 256), losses := [] }

theorem u36167 : Upper (D 6) (R 6) [34,68,136,20,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36168 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 70 140 56 19 357 325 453 325), lower := (rows 35 70 140 56 19 32 64 128 256), losses := [] }

theorem u36168 : Upper (D 6) (R 6) [34,68,136,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36169 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 289, targets := 4 },{ cop := 4, region := 322, targets := 32 }], pairs := [(0,2),(1,5),(3,2)], upper := (rows 35 70 140 56 21 355 323 451 323), lower := (rows 35 70 140 56 21 32 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 24 16 35 67 131 259), good := (rows 483 483 136 56 505 32 64 128 256) }] }

theorem u36169 : Upper (D 6) (R 6) [34,68,136,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36170 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 35 70 140 56 22 353 321 449 321), lower := (rows 35 70 140 56 22 32 64 128 256), losses := [] }

theorem u36170 : Upper (D 6) (R 6) [34,68,136,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36171 : Route 9 := (fun mask => (mask,id))

def c36171 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36171 : Upper (D 6) (R 6) [34,68,136,48,65] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,65] 13 (by decide) (choices 1) [1,2,4,256] r36171 c36171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20495
  · exact u20496
  · exact u20497
  · exact u20498

def b36172 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 70 140 56 82 293 325 389 261), lower := (rows 35 70 140 56 82 32 64 128 256), losses := [] }

theorem u36172 : Upper (D 6) (R 6) [34,68,136,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36173 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 35 70 140 56 84 291 323 387 259), lower := (rows 35 70 140 56 84 32 64 128 256), losses := [] }

theorem u36173 : Upper (D 6) (R 6) [34,68,136,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36174 : Route 9 := (fun mask => (mask,id))

def c36174 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36174 : Upper (D 6) (R 6) [34,68,136,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,257] 13 (by decide) (choices 1) [1,2,4,64] r36174 c36174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20499
  · exact u20500
  · exact u20501
  · exact u20502

def r36175 : Route 9 := (fun mask => (mask,id))

def c36175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36175 : Upper (D 6) (R 6) [34,68,136,48,258] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,258] 13 (by decide) (choices 1) [1,4,64] r36175 c36175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20503
  · exact u20504
  · exact u20505

def r36176 : Route 9 := (fun mask => (mask,id))

def c36176 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36176 : Upper (D 6) (R 6) [34,68,136,48,260] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,260] 13 (by decide) (choices 1) [1,2,64] r36176 c36176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20506
  · exact u20507
  · exact u20508

def r36177 : Route 9 := (fun mask => (mask,id))

def c36177 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36177 : Upper (D 6) (R 6) [34,68,136,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,320] 13 (by decide) (choices 1) [1,2,4] r36177 c36177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20509
  · exact u20510
  · exact u20511

def b36178 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 70 140 73 19 308 372 436 308), lower := (rows 35 70 140 73 19 32 64 128 256), losses := [] }

theorem u36178 : Upper (D 6) (R 6) [34,68,136,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36179 : PairBound 9 := { available := 306, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 70 140 73 21 306 370 434 306), lower := (rows 35 70 140 73 21 32 64 128 256), losses := [] }

theorem u36179 : Upper (D 6) (R 6) [34,68,136,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u36179
end Delivery.IrregularNine14.P06
