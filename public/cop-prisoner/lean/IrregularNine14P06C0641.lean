import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0405
import IrregularNine14P06C0406
import IrregularNine14P06C0407

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b38460 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 276 76 49 103 71 199 327), lower := (rows 35 138 276 76 49 32 64 128 256), losses := [] }

theorem u38460 : Upper (D 6) (R 6) [34,136,272,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38461 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 276 76 50 101 69 197 325), lower := (rows 35 138 276 76 50 32 64 128 256), losses := [] }

theorem u38461 : Upper (D 6) (R 6) [34,136,272,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38462 : Route 9 := (fun mask => (mask,id))

def c38462 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38462 : Upper (D 6) (R 6) [34,136,272,68,36] 13 := by
  apply FastRouting.sound _ _ [34,136,272,68,36] 13 (by decide) (choices 1) [1,2,64] r38462 c38462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24328
  · exact u24329
  · exact u24330

def r38463 : Route 9 := (fun mask => (mask,id))

def c38463 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38463 : Upper (D 6) (R 6) [34,136,272,68,65] 13 := by
  apply FastRouting.sound _ _ [34,136,272,68,65] 13 (by decide) (choices 1) [1,2,4] r38463 c38463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24331
  · exact u24332
  · exact u24333

def b38464 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 4, region := 293, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 138 276 76 82 37 101 165 293), lower := (rows 35 138 276 76 82 32 64 128 256), losses := [] }

theorem u38464 : Upper (D 6) (R 6) [34,136,272,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38465 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 276 76 84 35 99 163 291), lower := (rows 35 138 276 76 84 32 64 128 256), losses := [] }

theorem u38465 : Upper (D 6) (R 6) [34,136,272,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38466 : Route 9 := (fun mask => (mask,id))

def c38466 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38466 : Upper (D 6) (R 6) [34,136,272,68,96] 13 := by
  apply FastRouting.sound _ _ [34,136,272,68,96] 13 (by decide) (choices 1) [1,2,4] r38466 c38466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24334
  · exact u24335
  · exact u24336

def b38467 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 138 276 104 19 101 69 197 325), lower := (rows 35 138 276 104 19 32 64 128 256), losses := [] }

theorem u38467 : Upper (D 6) (R 6) [34,136,272,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38468 : Route 9 := (fun mask => (mask,id))

def c38468 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38468 : Upper (D 6) (R 6) [34,136,272,96,5] 13 := by
  apply FastRouting.sound _ _ [34,136,272,96,5] 13 (by decide) (choices 1) [1,2,4,64] r38468 c38468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24337
  · exact u24338
  · exact u24339
  · exact u24340

def r38469 : Route 9 := (fun mask => (mask,id))

def c38469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38469 : Upper (D 6) (R 6) [34,136,272,96,6] 13 := by
  apply FastRouting.sound _ _ [34,136,272,96,6] 13 (by decide) (choices 1) [1,4,64] r38469 c38469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24341
  · exact u24342
  · exact u24343

def r38470 : Route 9 := (fun mask => (mask,id))

def c38470 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38470 : Upper (D 6) (R 6) [34,136,272,96,65] 13 := by
  apply FastRouting.sound _ _ [34,136,272,96,65] 13 (by decide) (choices 1) [1,2,4] r38470 c38470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24344
  · exact u24345
  · exact u24346

def b38471 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 293, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 138 276 104 82 37 69 133 261), lower := (rows 35 138 276 104 82 32 64 128 256), losses := [] }

theorem u38471 : Upper (D 6) (R 6) [34,136,272,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38472 : Route 9 := (fun mask => (mask,id))

def c38472 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38472 : Upper (D 6) (R 6) [34,136,272,96,68] 13 := by
  apply FastRouting.sound _ _ [34,136,272,96,68] 13 (by decide) (choices 1) [1,2,4] r38472 c38472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24347
  · exact u24348
  · exact u24349

def b38473 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 292 13 19 116 84 212 340), lower := (rows 35 138 292 13 19 32 64 128 256), losses := [] }

theorem u38473 : Upper (D 6) (R 6) [34,136,288,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38474 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 66 },{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 35 138 292 13 21 114 82 210 338), lower := (rows 35 138 292 13 21 32 64 128 256), losses := [] }

theorem u38474 : Upper (D 6) (R 6) [34,136,288,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38475 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 138 292 13 22 113 81 209 337), lower := (rows 35 138 292 13 22 32 64 128 256), losses := [] }

theorem u38475 : Upper (D 6) (R 6) [34,136,288,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38476 : Route 9 := (fun mask => (mask,id))

def c38476 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38476 : Upper (D 6) (R 6) [34,136,288,5,65] 13 := by
  apply FastRouting.sound _ _ [34,136,288,5,65] 13 (by decide) (choices 1) [2,4,16,64] r38476 c38476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24350
  · exact u24351
  · exact u24352
  · exact u24353

def r38477 : Route 9 := (fun mask => (mask,id))

def c38477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38477 : Upper (D 6) (R 6) [34,136,288,5,66] 13 := by
  apply FastRouting.sound _ _ [34,136,288,5,66] 13 (by decide) (choices 1) [1,4,16,64] r38477 c38477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24354
  · exact u24355
  · exact u24356
  · exact u24357

def r38478 : Route 9 := (fun mask => (mask,id))

def c38478 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38478 : Upper (D 6) (R 6) [34,136,288,5,68] 13 := by
  apply FastRouting.sound _ _ [34,136,288,5,68] 13 (by decide) (choices 1) [1,2,16,64] r38478 c38478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24358
  · exact u24359
  · exact u24360
  · exact u24361

def b38479 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 138 292 14 21 113 81 209 337), lower := (rows 35 138 292 14 21 32 64 128 256), losses := [] }

theorem u38479 : Upper (D 6) (R 6) [34,136,288,6,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38480 : Route 9 := (fun mask => (mask,id))

def c38480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38480 : Upper (D 6) (R 6) [34,136,288,6,65] 13 := by
  apply FastRouting.sound _ _ [34,136,288,6,65] 13 (by decide) (choices 1) [1,4,16,64] r38480 c38480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24362
  · exact u24363
  · exact u24364
  · exact u24365

def r38481 : Route 9 := (fun mask => (mask,id))

def c38481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38481 : Upper (D 6) (R 6) [34,136,288,6,68] 13 := by
  apply FastRouting.sound _ _ [34,136,288,6,68] 13 (by decide) (choices 1) [1,16,64] r38481 c38481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24366
  · exact u24367
  · exact u24368

def b38482 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 138 292 25 19 100 68 196 324), lower := (rows 35 138 292 25 19 32 64 128 256), losses := [] }

theorem u38482 : Upper (D 6) (R 6) [34,136,288,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38483 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 138 292 25 21 102 70 198 326), lower := (rows 35 138 292 25 21 32 64 128 256), losses := [] }

theorem u38483 : Upper (D 6) (R 6) [34,136,288,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38484 : Route 9 := (fun mask => (mask,id))

def c38484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38484 : Upper (D 6) (R 6) [34,136,288,17,6] 13 := by
  apply FastRouting.sound _ _ [34,136,288,17,6] 13 (by decide) (choices 1) [1,4,64] r38484 c38484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24369
  · exact u24370
  · exact u24371

def b38485 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 138 292 25 81 102 70 198 326), lower := (rows 35 138 292 25 81 32 64 128 256), losses := [] }

theorem u38485 : Upper (D 6) (R 6) [34,136,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38486 : Route 9 := (fun mask => (mask,id))

def c38486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38486 : Upper (D 6) (R 6) [34,136,288,17,66] 13 := by
  apply FastRouting.sound _ _ [34,136,288,17,66] 13 (by decide) (choices 1) [1,4,64] r38486 c38486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24372
  · exact u24373
  · exact u24374

def r38487 : Route 9 := (fun mask => (mask,id))

def c38487 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38487 : Upper (D 6) (R 6) [34,136,288,17,68] 13 := by
  apply FastRouting.sound _ _ [34,136,288,17,68] 13 (by decide) (choices 1) [1,2,4,64] r38487 c38487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24375
  · exact u24376
  · exact u24377
  · exact u24378

def b38488 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 138 292 26 21 101 69 197 325), lower := (rows 35 138 292 26 21 32 64 128 256), losses := [] }

theorem u38488 : Upper (D 6) (R 6) [34,136,288,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38489 : Route 9 := (fun mask => (mask,id))

def c38489 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38489 : Upper (D 6) (R 6) [34,136,288,18,65] 13 := by
  apply FastRouting.sound _ _ [34,136,288,18,65] 13 (by decide) (choices 1) [1,4,64] r38489 c38489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24379
  · exact u24380
  · exact u24381

def r38490 : Route 9 := (fun mask => (mask,id))

def c38490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38490 : Upper (D 6) (R 6) [34,136,288,18,68] 13 := by
  apply FastRouting.sound _ _ [34,136,288,18,68] 13 (by decide) (choices 1) [1,4,64] r38490 c38490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24382
  · exact u24383
  · exact u24384

def b38491 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 292 28 19 101 69 197 325), lower := (rows 35 138 292 28 19 32 64 128 256), losses := [] }

theorem u38491 : Upper (D 6) (R 6) [34,136,288,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38492 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 138 292 28 21 99 67 195 323), lower := (rows 35 138 292 28 21 32 64 128 256), losses := [] }

theorem u38492 : Upper (D 6) (R 6) [34,136,288,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38493 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 292 28 22 97 65 193 321), lower := (rows 35 138 292 28 22 32 64 128 256), losses := [] }

theorem u38493 : Upper (D 6) (R 6) [34,136,288,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38494 : Route 9 := (fun mask => (mask,id))

def c38494 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38494 : Upper (D 6) (R 6) [34,136,288,20,65] 13 := by
  apply FastRouting.sound _ _ [34,136,288,20,65] 13 (by decide) (choices 1) [1,2,4,64] r38494 c38494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24385
  · exact u24386
  · exact u24387
  · exact u24388

def r38495 : Route 9 := (fun mask => (mask,id))

def c38495 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38495 : Upper (D 6) (R 6) [34,136,288,20,66] 13 := by
  apply FastRouting.sound _ _ [34,136,288,20,66] 13 (by decide) (choices 1) [1,4,64] r38495 c38495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24389
  · exact u24390
  · exact u24391

def b38496 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 292 28 84 99 67 195 323), lower := (rows 35 138 292 28 84 32 64 128 256), losses := [] }

theorem u38496 : Upper (D 6) (R 6) [34,136,288,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38497 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 292 73 19 116 84 212 340), lower := (rows 35 138 292 73 19 32 64 128 256), losses := [] }

theorem u38497 : Upper (D 6) (R 6) [34,136,288,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38498 : Route 9 := (fun mask => (mask,id))

def c38498 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38498 : Upper (D 6) (R 6) [34,136,288,65,5] 13 := by
  apply FastRouting.sound _ _ [34,136,288,65,5] 13 (by decide) (choices 1) [2,4,16,64] r38498 c38498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24392
  · exact u24393
  · exact u24394
  · exact u24395

def r38499 : Route 9 := (fun mask => (mask,id))

def c38499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38499 : Upper (D 6) (R 6) [34,136,288,65,6] 13 := by
  apply FastRouting.sound _ _ [34,136,288,65,6] 13 (by decide) (choices 1) [1,4,16,64] r38499 c38499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24396
  · exact u24397
  · exact u24398
  · exact u24399

def b38500 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 35 138 292 73 81 54 86 150 278), lower := (rows 35 138 292 73 81 32 64 128 256), losses := [] }

theorem u38500 : Upper (D 6) (R 6) [34,136,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38501 : Route 9 := (fun mask => (mask,id))

def c38501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38501 : Upper (D 6) (R 6) [34,136,288,65,66] 13 := by
  apply FastRouting.sound _ _ [34,136,288,65,66] 13 (by decide) (choices 1) [1,4,16] r38501 c38501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24400
  · exact u24401
  · exact u24402

def r38502 : Route 9 := (fun mask => (mask,id))

def c38502 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38502 : Upper (D 6) (R 6) [34,136,288,65,68] 13 := by
  apply FastRouting.sound _ _ [34,136,288,65,68] 13 (by decide) (choices 1) [1,2,4,16] r38502 c38502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24403
  · exact u24404
  · exact u24405
  · exact u24406

def b38503 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 138 292 74 21 117 85 213 341), lower := (rows 35 138 292 74 21 32 64 128 256), losses := [] }

theorem u38503 : Upper (D 6) (R 6) [34,136,288,66,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38504 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 292, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 292 74 81 53 85 149 277), lower := (rows 35 138 292 74 81 32 64 128 256), losses := [] }

theorem u38504 : Upper (D 6) (R 6) [34,136,288,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38505 : Route 9 := (fun mask => (mask,id))

def c38505 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38505 : Upper (D 6) (R 6) [34,136,288,66,68] 13 := by
  apply FastRouting.sound _ _ [34,136,288,66,68] 13 (by decide) (choices 1) [1,4,16] r38505 c38505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24407
  · exact u24408
  · exact u24409

def b38506 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 292 76 19 117 85 213 341), lower := (rows 35 138 292 76 19 32 64 128 256), losses := [] }

theorem u38506 : Upper (D 6) (R 6) [34,136,288,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38507 : Route 9 := (fun mask => (mask,id))

def c38507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38507 : Upper (D 6) (R 6) [34,136,288,68,5] 13 := by
  apply FastRouting.sound _ _ [34,136,288,68,5] 13 (by decide) (choices 1) [1,2,16,64] r38507 c38507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24410
  · exact u24411
  · exact u24412
  · exact u24413

def r38508 : Route 9 := (fun mask => (mask,id))

def c38508 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38508 : Upper (D 6) (R 6) [34,136,288,68,6] 13 := by
  apply FastRouting.sound _ _ [34,136,288,68,6] 13 (by decide) (choices 1) [1,16,64] r38508 c38508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24414
  · exact u24415
  · exact u24416

def r38509 : Route 9 := (fun mask => (mask,id))

def c38509 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38509 : Upper (D 6) (R 6) [34,136,288,68,65] 13 := by
  apply FastRouting.sound _ _ [34,136,288,68,65] 13 (by decide) (choices 1) [1,2,4,16] r38509 c38509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24417
  · exact u24418
  · exact u24419
  · exact u24420

def r38510 : Route 9 := (fun mask => (mask,id))

def c38510 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38510 : Upper (D 6) (R 6) [34,136,288,68,66] 13 := by
  apply FastRouting.sound _ _ [34,136,288,68,66] 13 (by decide) (choices 1) [1,4,16] r38510 c38510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24421
  · exact u24422
  · exact u24423

def b38511 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 292 76 84 51 83 147 275), lower := (rows 35 138 292 76 84 32 64 128 256), losses := [] }

theorem u38511 : Upper (D 6) (R 6) [34,136,288,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38512 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 292 88 19 101 69 197 325), lower := (rows 35 138 292 88 19 32 64 128 256), losses := [] }

theorem u38512 : Upper (D 6) (R 6) [34,136,288,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38513 : Route 9 := (fun mask => (mask,id))

def c38513 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38513 : Upper (D 6) (R 6) [34,136,288,80,5] 13 := by
  apply FastRouting.sound _ _ [34,136,288,80,5] 13 (by decide) (choices 1) [1,2,4,64] r38513 c38513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24424
  · exact u24425
  · exact u24426
  · exact u24427

def r38514 : Route 9 := (fun mask => (mask,id))

def c38514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38514 : Upper (D 6) (R 6) [34,136,288,80,6] 13 := by
  apply FastRouting.sound _ _ [34,136,288,80,6] 13 (by decide) (choices 1) [1,4,64] r38514 c38514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24428
  · exact u24429
  · exact u24430

def b38515 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 138 292 88 81 39 71 135 263), lower := (rows 35 138 292 88 81 32 64 128 256), losses := [] }

theorem u38515 : Upper (D 6) (R 6) [34,136,288,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38516 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 138 292 88 82 37 69 133 261), lower := (rows 35 138 292 88 82 32 64 128 256), losses := [] }

theorem u38516 : Upper (D 6) (R 6) [34,136,288,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38517 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 138 292 88 84 39 71 135 263), lower := (rows 35 138 292 88 84 32 64 128 256), losses := [] }

theorem u38517 : Upper (D 6) (R 6) [34,136,288,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38518 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 324 13 19 116 116 244 372), lower := (rows 35 138 324 13 19 32 64 128 256), losses := [] }

theorem u38518 : Upper (D 6) (R 6) [34,136,320,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38519 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 138 324 13 21 114 114 242 370), lower := (rows 35 138 324 13 21 32 64 128 256), losses := [] }

theorem u38519 : Upper (D 6) (R 6) [34,136,320,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u38519
end Delivery.IrregularNine14.P06
