import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0322
import IrregularNine14P07C0323
import IrregularNine14P07C0324

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34560 : Route 9 := (fun mask => (mask,id))

def c34560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34560 : Upper (D 7) (R 7) [34,68,129,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,320] 13 (by decide) (choices 1) [1,2,8,16] r34560 c34560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19341
  · exact u19342
  · exact u19343
  · exact u19344

def r34561 : Route 9 := (fun mask => (mask,id))

def c34561 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34561 : Upper (D 7) (R 7) [34,68,129,192,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,257] 13 (by decide) (choices 1) [2,8,16] r34561 c34561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19345
  · exact u19346
  · exact u19347

def r34562 : Route 9 := (fun mask => (mask,id))

def c34562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34562 : Upper (D 7) (R 7) [34,68,129,192,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,258] 13 (by decide) (choices 1) [1,8,16] r34562 c34562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19348
  · exact u19349
  · exact u19350

def r34563 : Route 9 := (fun mask => (mask,id))

def c34563 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34563 : Upper (D 7) (R 7) [34,68,129,192,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,264] 13 (by decide) (choices 1) [1,2,16] r34563 c34563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19351
  · exact u19352
  · exact u19353

def r34564 : Route 9 := (fun mask => (mask,id))

def c34564 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34564 : Upper (D 7) (R 7) [34,68,129,192,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,288] 13 (by decide) (choices 1) [1,2,8,16] r34564 c34564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19354
  · exact u19355
  · exact u19356
  · exact u19357

def b34565 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 134 25 25 480 480 480 480), lower := (rows 35 70 134 25 25 32 64 128 256), losses := [] }

theorem u34565 : Upper (D 7) (R 7) [34,68,130,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34566 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 134 25 49 488 456 456 456), lower := (rows 35 70 134 25 49 32 64 128 256), losses := [] }

theorem u34566 : Upper (D 7) (R 7) [34,68,130,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34567 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 134 25 56 481 449 449 449), lower := (rows 35 70 134 25 56 32 64 128 256), losses := [] }

theorem u34567 : Upper (D 7) (R 7) [34,68,130,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34568 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0),(2,0),(3,1),(4,1)], upper := (rows 35 70 134 25 81 424 488 424 424), lower := (rows 35 70 134 25 81 32 64 128 256), losses := [] }

theorem u34568 : Upper (D 7) (R 7) [34,68,130,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34569 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 35 70 134 25 88 417 481 417 417), lower := (rows 35 70 134 25 88 32 64 128 256), losses := [] }

theorem u34569 : Upper (D 7) (R 7) [34,68,130,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34570 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 134 25 112 425 457 393 393), lower := (rows 35 70 134 25 112 32 64 128 256), losses := [] }

theorem u34570 : Upper (D 7) (R 7) [34,68,130,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34571 : PairBound 9 := { available := 360, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0),(2,0),(3,1),(4,1)], upper := (rows 35 70 134 25 145 360 360 488 360), lower := (rows 35 70 134 25 145 32 64 128 256), losses := [] }

theorem u34571 : Upper (D 7) (R 7) [34,68,130,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34571 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34572 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(3,1),(4,1)], upper := (rows 35 70 134 25 152 353 353 481 353), lower := (rows 35 70 134 25 152 32 64 128 256), losses := [] }

theorem u34572 : Upper (D 7) (R 7) [34,68,130,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34573 : PairBound 9 := { available := 329, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 134 25 176 361 329 457 329), lower := (rows 35 70 134 25 176 32 64 128 256), losses := [] }

theorem u34573 : Upper (D 7) (R 7) [34,68,130,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34574 : PairBound 9 := { available := 297, camps := [{ cop := 4, region := 6, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 134 25 208 297 361 425 297), lower := (rows 35 70 134 25 208 32 64 128 256), losses := [] }

theorem u34574 : Upper (D 7) (R 7) [34,68,130,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34575 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 224 },{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 134 25 273 232 232 232 488), lower := (rows 35 70 134 25 273 32 64 128 256), losses := [] }

theorem u34575 : Upper (D 7) (R 7) [34,68,130,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34576 : Route 9 := (fun mask => (mask,id))

def c34576 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34576 : Upper (D 7) (R 7) [34,68,130,17,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,264] 13 (by decide) (choices 1) [1,64,128] r34576 c34576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19358
  · exact u19359
  · exact u19360

def b34577 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 134 25 304 233 201 201 457), lower := (rows 35 70 134 25 304 32 64 128 256), losses := [] }

theorem u34577 : Upper (D 7) (R 7) [34,68,130,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34578 : Route 9 := (fun mask => (mask,id))

def c34578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34578 : Upper (D 7) (R 7) [34,68,130,17,320] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,320] 13 (by decide) (choices 1) [1,8,128] r34578 c34578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19361
  · exact u19362
  · exact u19363

def r34579 : Route 9 := (fun mask => (mask,id))

def c34579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34579 : Upper (D 7) (R 7) [34,68,130,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,384] 13 (by decide) (choices 1) [1,8,64] r34579 c34579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19364
  · exact u19365
  · exact u19366

def b34580 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 134 41 81 440 472 408 408), lower := (rows 35 70 134 41 81 32 64 128 256), losses := [] }

theorem u34580 : Upper (D 7) (R 7) [34,68,130,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34581 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 134 41 88 433 465 401 401), lower := (rows 35 70 134 41 88 32 64 128 256), losses := [] }

theorem u34581 : Upper (D 7) (R 7) [34,68,130,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34582 : PairBound 9 := { available := 344, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 134 41 145 376 344 472 344), lower := (rows 35 70 134 41 145 32 64 128 256), losses := [] }

theorem u34582 : Upper (D 7) (R 7) [34,68,130,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34583 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 134 41 152 369 337 465 337), lower := (rows 35 70 134 41 152 32 64 128 256), losses := [] }

theorem u34583 : Upper (D 7) (R 7) [34,68,130,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34583 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34584 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 134 41 273 248 216 216 472), lower := (rows 35 70 134 41 273 32 64 128 256), losses := [] }

theorem u34584 : Upper (D 7) (R 7) [34,68,130,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34585 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 134 41 280 241 209 209 465), lower := (rows 35 70 134 41 280 32 64 128 256), losses := [] }

theorem u34585 : Upper (D 7) (R 7) [34,68,130,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34585 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34586 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 134 41 336 185 217 153 409), lower := (rows 35 70 134 41 336 32 64 128 256), losses := [] }

theorem u34586 : Upper (D 7) (R 7) [34,68,130,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34587 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 470, targets := 32 },{ cop := 0, region := 8, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 134 41 400 121 89 217 345), lower := (rows 35 70 134 41 400 32 64 128 256), losses := [] }

theorem u34587 : Upper (D 7) (R 7) [34,68,130,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34588 : Route 9 := (fun mask => (mask,id))

def c34588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34588 : Upper (D 7) (R 7) [34,68,130,48,65] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,65] 13 (by decide) (choices 1) [1,8,128,256] r34588 c34588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19367
  · exact u19368
  · exact u19369
  · exact u19370

def b34589 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 134 56 88 417 449 385 385), lower := (rows 35 70 134 56 88 32 64 128 256), losses := [] }

theorem u34589 : Upper (D 7) (R 7) [34,68,130,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34590 : Route 9 := (fun mask => (mask,id))

def c34590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34590 : Upper (D 7) (R 7) [34,68,130,48,129] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,129] 13 (by decide) (choices 1) [1,8,64,256] r34590 c34590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19371
  · exact u19372
  · exact u19373
  · exact u19374

def b34591 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 134 56 152 353 321 449 321), lower := (rows 35 70 134 56 152 32 64 128 256), losses := [] }

theorem u34591 : Upper (D 7) (R 7) [34,68,130,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34592 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 6, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 134 56 208 297 329 393 265), lower := (rows 35 70 134 56 208 32 64 128 256), losses := [] }

theorem u34592 : Upper (D 7) (R 7) [34,68,130,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34593 : Route 9 := (fun mask => (mask,id))

def c34593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34593 : Upper (D 7) (R 7) [34,68,130,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,257] 13 (by decide) (choices 1) [1,8,64,128] r34593 c34593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19375
  · exact u19376
  · exact u19377
  · exact u19378

def b34594 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 134 56 280 225 193 193 449), lower := (rows 35 70 134 56 280 32 64 128 256), losses := [] }

theorem u34594 : Upper (D 7) (R 7) [34,68,130,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34595 : Route 9 := (fun mask => (mask,id))

def c34595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34595 : Upper (D 7) (R 7) [34,68,130,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,320] 13 (by decide) (choices 1) [1,8,128] r34595 c34595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19379
  · exact u19380
  · exact u19381

def r34596 : Route 9 := (fun mask => (mask,id))

def c34596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34596 : Upper (D 7) (R 7) [34,68,130,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,130,48,384] 13 (by decide) (choices 1) [1,8,64] r34596 c34596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19382
  · exact u19383
  · exact u19384

def b34597 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 432, targets := 64 },{ cop := 4, region := 360, targets := 128 }], pairs := [(3,1),(3,7),(4,1),(4,6)], upper := (rows 35 70 134 73 145 312 376 440 312), lower := (rows 35 70 134 73 145 32 64 128 256), losses := [] }

theorem u34597 : Upper (D 7) (R 7) [34,68,130,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34598 : Route 9 := (fun mask => (mask,id))

def c34598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34598 : Upper (D 7) (R 7) [34,68,130,65,136] 13 := by
  apply FastRouting.sound _ _ [34,68,130,65,136] 13 (by decide) (choices 1) [1,16,256] r34598 c34598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19385
  · exact u19386
  · exact u19387

def r34599 : Route 9 := (fun mask => (mask,id))

def c34599 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34599 : Upper (D 7) (R 7) [34,68,130,65,160] 13 := by
  apply FastRouting.sound _ _ [34,68,130,65,160] 13 (by decide) (choices 1) [1,8,16,256] r34599 c34599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19388
  · exact u19389
  · exact u19390
  · exact u19391

def r34600 : Route 9 := (fun mask => (mask,id))

def c34600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34600 : Upper (D 7) (R 7) [34,68,130,65,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,65,257] 13 (by decide) (choices 1) [8,16,128] r34600 c34600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19392
  · exact u19393
  · exact u19394

def r34601 : Route 9 := (fun mask => (mask,id))

def c34601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34601 : Upper (D 7) (R 7) [34,68,130,65,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,65,264] 13 (by decide) (choices 1) [1,16,128] r34601 c34601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19395
  · exact u19396
  · exact u19397

def r34602 : Route 9 := (fun mask => (mask,id))

def c34602 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34602 : Upper (D 7) (R 7) [34,68,130,65,288] 13 := by
  apply FastRouting.sound _ _ [34,68,130,65,288] 13 (by decide) (choices 1) [1,8,16,128] r34602 c34602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19398
  · exact u19399
  · exact u19400
  · exact u19401

def r34603 : Route 9 := (fun mask => (mask,id))

def c34603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34603 : Upper (D 7) (R 7) [34,68,130,65,384] 13 := by
  apply FastRouting.sound _ _ [34,68,130,65,384] 13 (by decide) (choices 1) [1,8,16] r34603 c34603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19402
  · exact u19403
  · exact u19404

def r34604 : Route 9 := (fun mask => (mask,id))

def c34604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34604 : Upper (D 7) (R 7) [34,68,130,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,129] 13 (by decide) (choices 1) [1,8,256] r34604 c34604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19405
  · exact u19406
  · exact u19407

def b34605 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 35 70 134 88 152 289 353 417 289), lower := (rows 35 70 134 88 152 32 64 128 256), losses := [] }

theorem u34605 : Upper (D 7) (R 7) [34,68,130,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34606 : Route 9 := (fun mask => (mask,id))

def c34606 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34606 : Upper (D 7) (R 7) [34,68,130,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,160] 13 (by decide) (choices 1) [1,8,256] r34606 c34606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19408
  · exact u19409
  · exact u19410

def r34607 : Route 9 := (fun mask => (mask,id))

def c34607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34607 : Upper (D 7) (R 7) [34,68,130,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,257] 13 (by decide) (choices 1) [1,8,128] r34607 c34607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19411
  · exact u19412
  · exact u19413

def b34608 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 35 70 134 88 280 161 225 161 417), lower := (rows 35 70 134 88 280 32 64 128 256), losses := [] }

theorem u34608 : Upper (D 7) (R 7) [34,68,130,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34609 : Route 9 := (fun mask => (mask,id))

def c34609 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34609 : Upper (D 7) (R 7) [34,68,130,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,288] 13 (by decide) (choices 1) [1,8,128] r34609 c34609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19414
  · exact u19415
  · exact u19416

def r34610 : Route 9 := (fun mask => (mask,id))

def c34610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34610 : Upper (D 7) (R 7) [34,68,130,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,130,80,384] 13 (by decide) (choices 1) [1,8] r34610 c34610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19417
  · exact u19418

def r34611 : Route 9 := (fun mask => (mask,id))

def c34611 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34611 : Upper (D 7) (R 7) [34,68,130,96,129] 13 := by
  apply FastRouting.sound _ _ [34,68,130,96,129] 13 (by decide) (choices 1) [1,8,16,256] r34611 c34611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19419
  · exact u19420
  · exact u19421
  · exact u19422

def r34612 : Route 9 := (fun mask => (mask,id))

def c34612 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34612 : Upper (D 7) (R 7) [34,68,130,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,130,96,136] 13 (by decide) (choices 1) [1,16,256] r34612 c34612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19423
  · exact u19424
  · exact u19425

def r34613 : Route 9 := (fun mask => (mask,id))

def c34613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34613 : Upper (D 7) (R 7) [34,68,130,96,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,96,257] 13 (by decide) (choices 1) [1,8,16,128] r34613 c34613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19426
  · exact u19427
  · exact u19428
  · exact u19429

def r34614 : Route 9 := (fun mask => (mask,id))

def c34614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34614 : Upper (D 7) (R 7) [34,68,130,96,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,96,264] 13 (by decide) (choices 1) [1,16,128] r34614 c34614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19430
  · exact u19431
  · exact u19432

def r34615 : Route 9 := (fun mask => (mask,id))

def c34615 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34615 : Upper (D 7) (R 7) [34,68,130,96,384] 13 := by
  apply FastRouting.sound _ _ [34,68,130,96,384] 13 (by decide) (choices 1) [1,8,16] r34615 c34615
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19433
  · exact u19434
  · exact u19435

def r34616 : Route 9 := (fun mask => (mask,id))

def c34616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34616 : Upper (D 7) (R 7) [34,68,130,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,130,129,257] 13 (by decide) (choices 1) [8,16,64] r34616 c34616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19436
  · exact u19437
  · exact u19438

def r34617 : Route 9 := (fun mask => (mask,id))

def c34617 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34617 : Upper (D 7) (R 7) [34,68,130,129,264] 13 := by
  apply FastRouting.sound _ _ [34,68,130,129,264] 13 (by decide) (choices 1) [1,16,64] r34617 c34617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19439
  · exact u19440
  · exact u19441

def r34618 : Route 9 := (fun mask => (mask,id))

def c34618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34618 : Upper (D 7) (R 7) [34,68,130,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,130,129,288] 13 (by decide) (choices 1) [1,8,16,64] r34618 c34618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19442
  · exact u19443
  · exact u19444
  · exact u19445

def r34619 : Route 9 := (fun mask => (mask,id))

def c34619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34619 : Upper (D 7) (R 7) [34,68,130,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,130,129,320] 13 (by decide) (choices 1) [1,8,16] r34619 c34619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19446
  · exact u19447
  · exact u19448

#print axioms u34619
end Delivery.IrregularNine14.P07
