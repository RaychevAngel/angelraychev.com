import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0321
import IrregularNine14P06C0322
import IrregularNine14P06C0323

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35520 : Route 9 := (fun mask => (mask,id))

def c35520 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35520 : Upper (D 6) (R 6) [24,160,320,6,36] 13 := by
  apply FastRouting.sound _ _ [24,160,320,6,36] 13 (by decide) (choices 1) [1,2,64] r35520 c35520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19293
  · exact u19294
  · exact u19295

def r35521 : Route 9 := (fun mask => (mask,id))

def c35521 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35521 : Upper (D 6) (R 6) [24,160,320,6,96] 13 := by
  apply FastRouting.sound _ _ [24,160,320,6,96] 13 (by decide) (choices 1) [1,2,4] r35521 c35521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19296
  · exact u19297
  · exact u19298

def b35522 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 1, region := 324, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 162 324 41 81 38 70 134 262), lower := (rows 25 162 324 41 81 32 64 128 256), losses := [] }

theorem u35522 : Upper (D 6) (R 6) [24,160,320,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35523 : Route 9 := (fun mask => (mask,id))

def c35523 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35523 : Upper (D 6) (R 6) [24,160,320,33,66] 13 := by
  apply FastRouting.sound _ _ [24,160,320,33,66] 13 (by decide) (choices 1) [1,2,4] r35523 c35523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19299
  · exact u19300
  · exact u19301

def b35524 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 162 324 41 84 39 71 135 263), lower := (rows 25 162 324 41 84 32 64 128 256), losses := [] }

theorem u35524 : Upper (D 6) (R 6) [24,160,320,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35525 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 162 324 42 82 37 69 133 261), lower := (rows 25 162 324 42 82 32 64 128 256), losses := [] }

theorem u35525 : Upper (D 6) (R 6) [24,160,320,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35526 : Route 9 := (fun mask => (mask,id))

def c35526 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35526 : Upper (D 6) (R 6) [24,160,320,36,66] 13 := by
  apply FastRouting.sound _ _ [24,160,320,36,66] 13 (by decide) (choices 1) [1,2,4] r35526 c35526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19302
  · exact u19303
  · exact u19304

def b35527 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 25 22 484 452 452 452), lower := (rows 35 67 44 25 22 32 64 128 256), losses := [] }

theorem u35527 : Upper (D 6) (R 6) [34,65,40,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35528 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 67 44 25 82 420 452 388 388), lower := (rows 35 67 44 25 82 32 64 128 256), losses := [] }

theorem u35528 : Upper (D 6) (R 6) [34,65,40,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35529 : PairBound 9 := { available := 390, camps := [], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 25 84 422 454 390 390), lower := (rows 35 67 44 25 84 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 11 18 32 64 128 256), good := (rows 61 93 44 29 84 32 64 128 256) }] }

theorem u35529 : Upper (D 6) (R 6) [34,65,40,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35530 : Route 9 := (fun mask => (mask,id))

def c35530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35530 : Upper (D 6) (R 6) [34,65,40,17,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,17,130] 13 (by decide) (choices 1) [4,64,256] r35530 c35530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19305
  · exact u19306
  · exact u19307

def r35531 : Route 9 := (fun mask => (mask,id))

def c35531 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35531 : Upper (D 6) (R 6) [34,65,40,17,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,17,132] 13 (by decide) (choices 1) [2,4,64,256] r35531 c35531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19308
  · exact u19309
  · exact u19310
  · exact u19311

def r35532 : Route 9 := (fun mask => (mask,id))

def c35532 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35532 : Upper (D 6) (R 6) [34,65,40,17,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,17,192] 13 (by decide) (choices 1) [2,4,256] r35532 c35532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19312
  · exact u19313
  · exact u19314

def r35533 : Route 9 := (fun mask => (mask,id))

def c35533 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35533 : Upper (D 6) (R 6) [34,65,40,17,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,17,384] 13 (by decide) (choices 1) [2,4,64] r35533 c35533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19315
  · exact u19316
  · exact u19317

def b35534 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 26 21 484 452 452 452), lower := (rows 35 67 44 26 21 32 64 128 256), losses := [] }

theorem u35534 : Upper (D 6) (R 6) [34,65,40,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35535 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 67 44 26 81 420 452 388 388), lower := (rows 35 67 44 26 81 32 64 128 256), losses := [] }

theorem u35535 : Upper (D 6) (R 6) [34,65,40,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35536 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,0),(2,6)], upper := (rows 35 67 44 26 84 421 453 389 389), lower := (rows 35 67 44 26 84 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 11 18 32 64 128 256), good := (rows 62 94 44 26 84 32 64 128 256) }] }

theorem u35536 : Upper (D 6) (R 6) [34,65,40,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35536 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35537 : Route 9 := (fun mask => (mask,id))

def c35537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35537 : Upper (D 6) (R 6) [34,65,40,18,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,18,129] 13 (by decide) (choices 1) [4,64,256] r35537 c35537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19318
  · exact u19319
  · exact u19320

def r35538 : Route 9 := (fun mask => (mask,id))

def c35538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35538 : Upper (D 6) (R 6) [34,65,40,18,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,18,132] 13 (by decide) (choices 1) [1,4,64,256] r35538 c35538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19321
  · exact u19322
  · exact u19323
  · exact u19324

def r35539 : Route 9 := (fun mask => (mask,id))

def c35539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35539 : Upper (D 6) (R 6) [34,65,40,18,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,18,192] 13 (by decide) (choices 1) [1,4,256] r35539 c35539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19325
  · exact u19326
  · exact u19327

def r35540 : Route 9 := (fun mask => (mask,id))

def c35540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35540 : Upper (D 6) (R 6) [34,65,40,18,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,18,384] 13 (by decide) (choices 1) [1,4,64] r35540 c35540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19328
  · exact u19329
  · exact u19330

def b35541 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 44 28 19 484 452 452 452), lower := (rows 35 67 44 28 19 32 64 128 256), losses := [] }

theorem u35541 : Upper (D 6) (R 6) [34,65,40,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35542 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 28, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 35 67 44 28 21 482 450 450 450), lower := (rows 35 67 44 28 21 32 64 128 256), losses := [] }

theorem u35542 : Upper (D 6) (R 6) [34,65,40,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35543 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 44 28 22 481 449 449 449), lower := (rows 35 67 44 28 22 32 64 128 256), losses := [] }

theorem u35543 : Upper (D 6) (R 6) [34,65,40,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35544 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 16, targets := 36 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,5)], upper := (rows 35 67 44 28 81 422 454 390 390), lower := (rows 35 67 44 28 81 32 64 128 256), losses := [] }

theorem u35544 : Upper (D 6) (R 6) [34,65,40,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35545 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 44 28 82 421 453 389 389), lower := (rows 35 67 44 28 82 32 64 128 256), losses := [] }

theorem u35545 : Upper (D 6) (R 6) [34,65,40,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35546 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 44 28 84 419 451 387 387), lower := (rows 35 67 44 28 84 32 64 128 256), losses := [] }

theorem u35546 : Upper (D 6) (R 6) [34,65,40,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35547 : Route 9 := (fun mask => (mask,id))

def c35547 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35547 : Upper (D 6) (R 6) [34,65,40,20,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,20,129] 13 (by decide) (choices 1) [2,4,64,256] r35547 c35547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19331
  · exact u19332
  · exact u19333
  · exact u19334

def r35548 : Route 9 := (fun mask => (mask,id))

def c35548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35548 : Upper (D 6) (R 6) [34,65,40,20,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,20,130] 13 (by decide) (choices 1) [1,4,64,256] r35548 c35548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19335
  · exact u19336
  · exact u19337
  · exact u19338

def b35549 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 44 28 148 355 323 451 323), lower := (rows 35 67 44 28 148 32 64 128 256), losses := [] }

theorem u35549 : Upper (D 6) (R 6) [34,65,40,20,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35550 : Route 9 := (fun mask => (mask,id))

def c35550 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35550 : Upper (D 6) (R 6) [34,65,40,20,192] 13 := by
  apply FastRouting.sound _ _ [34,65,40,20,192] 13 (by decide) (choices 1) [1,2,4,256] r35550 c35550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19339
  · exact u19340
  · exact u19341
  · exact u19342

def r35551 : Route 9 := (fun mask => (mask,id))

def c35551 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35551 : Upper (D 6) (R 6) [34,65,40,20,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,20,384] 13 (by decide) (choices 1) [1,2,4,64] r35551 c35551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19343
  · exact u19344
  · exact u19345
  · exact u19346

def b35552 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 24, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 67 44 88 19 420 452 388 388), lower := (rows 35 67 44 88 19 32 64 128 256), losses := [] }

theorem u35552 : Upper (D 6) (R 6) [34,65,40,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35553 : PairBound 9 := { available := 390, camps := [{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(2,1),(3,5)], upper := (rows 35 67 44 88 21 422 454 390 390), lower := (rows 35 67 44 88 21 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 10 19 32 64 128 256), good := (rows 61 93 44 88 21 32 64 128 256) }] }

theorem u35553 : Upper (D 6) (R 6) [34,65,40,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35554 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6),(2,0),(3,0)], upper := (rows 35 67 44 88 22 421 453 389 389), lower := (rows 35 67 44 88 22 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 10 19 32 64 128 256), good := (rows 62 94 44 88 30 32 64 128 256) }] }

theorem u35554 : Upper (D 6) (R 6) [34,65,40,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35555 : Route 9 := (fun mask => (mask,id))

def c35555 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35555 : Upper (D 6) (R 6) [34,65,40,80,129] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,129] 13 (by decide) (choices 1) [2,4,256] r35555 c35555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19347
  · exact u19348
  · exact u19349

def r35556 : Route 9 := (fun mask => (mask,id))

def c35556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35556 : Upper (D 6) (R 6) [34,65,40,80,130] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,130] 13 (by decide) (choices 1) [1,4,256] r35556 c35556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19350
  · exact u19351
  · exact u19352

def r35557 : Route 9 := (fun mask => (mask,id))

def c35557 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35557 : Upper (D 6) (R 6) [34,65,40,80,132] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,132] 13 (by decide) (choices 1) [1,2,4,256] r35557 c35557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19353
  · exact u19354
  · exact u19355
  · exact u19356

def r35558 : Route 9 := (fun mask => (mask,id))

def c35558 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35558 : Upper (D 6) (R 6) [34,65,40,80,384] 13 := by
  apply FastRouting.sound _ _ [34,65,40,80,384] 13 (by decide) (choices 1) [1,2,4] r35558 c35558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19357
  · exact u19358
  · exact u19359

def r35559 : Route 9 := (fun mask => (mask,id))

def c35559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u35559 : Upper (D 6) (R 6) [34,65,40,129,6] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,6] 13 (by decide) (choices 1) [4,16,64,256] r35559 c35559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19360
  · exact u19361
  · exact u19362
  · exact u19363

def b35560 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 44 137 82 308 340 404 276), lower := (rows 35 67 44 137 82 32 64 128 256), losses := [] }

theorem u35560 : Upper (D 6) (R 6) [34,65,40,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35561 : Route 9 := (fun mask => (mask,id))

def c35561 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35561 : Upper (D 6) (R 6) [34,65,40,129,68] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,68] 13 (by decide) (choices 1) [2,4,16,256] r35561 c35561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19364
  · exact u19365
  · exact u19366
  · exact u19367

def r35562 : Route 9 := (fun mask => (mask,id))

def c35562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35562 : Upper (D 6) (R 6) [34,65,40,129,258] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,258] 13 (by decide) (choices 1) [4,16,64] r35562 c35562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19368
  · exact u19369
  · exact u19370

def r35563 : Route 9 := (fun mask => (mask,id))

def c35563 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35563 : Upper (D 6) (R 6) [34,65,40,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,260] 13 (by decide) (choices 1) [2,4,16,64] r35563 c35563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19371
  · exact u19372
  · exact u19373
  · exact u19374

def r35564 : Route 9 := (fun mask => (mask,id))

def c35564 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35564 : Upper (D 6) (R 6) [34,65,40,129,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,129,320] 13 (by decide) (choices 1) [2,4,16] r35564 c35564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19375
  · exact u19376
  · exact u19377

def r35565 : Route 9 := (fun mask => (mask,id))

def c35565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u35565 : Upper (D 6) (R 6) [34,65,40,130,5] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,5] 13 (by decide) (choices 1) [4,16,64,256] r35565 c35565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19378
  · exact u19379
  · exact u19380
  · exact u19381

def b35566 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 16, targets := 36 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,5)], upper := (rows 35 67 44 138 81 308 340 404 276), lower := (rows 35 67 44 138 81 32 64 128 256), losses := [] }

theorem u35566 : Upper (D 6) (R 6) [34,65,40,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35567 : Route 9 := (fun mask => (mask,id))

def c35567 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35567 : Upper (D 6) (R 6) [34,65,40,130,68] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,68] 13 (by decide) (choices 1) [1,4,16,256] r35567 c35567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19382
  · exact u19383
  · exact u19384
  · exact u19385

def r35568 : Route 9 := (fun mask => (mask,id))

def c35568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35568 : Upper (D 6) (R 6) [34,65,40,130,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,257] 13 (by decide) (choices 1) [4,16,64] r35568 c35568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19386
  · exact u19387
  · exact u19388

def r35569 : Route 9 := (fun mask => (mask,id))

def c35569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35569 : Upper (D 6) (R 6) [34,65,40,130,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,260] 13 (by decide) (choices 1) [1,4,16,64] r35569 c35569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19389
  · exact u19390
  · exact u19391
  · exact u19392

def r35570 : Route 9 := (fun mask => (mask,id))

def c35570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35570 : Upper (D 6) (R 6) [34,65,40,130,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,130,320] 13 (by decide) (choices 1) [1,4,16] r35570 c35570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19393
  · exact u19394
  · exact u19395

def b35571 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 44 140 19 372 340 468 340), lower := (rows 35 67 44 140 19 32 64 128 256), losses := [] }

theorem u35571 : Upper (D 6) (R 6) [34,65,40,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35572 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 355, targets := 4 },{ cop := 4, region := 322, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 67 44 140 21 370 338 466 338), lower := (rows 35 67 44 140 21 32 64 128 256), losses := [] }

theorem u35572 : Upper (D 6) (R 6) [34,65,40,132,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35573 : Route 9 := (fun mask => (mask,id))

def c35573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u35573 : Upper (D 6) (R 6) [34,65,40,132,6] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,6] 13 (by decide) (choices 1) [1,16,64,256] r35573 c35573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19396
  · exact u19397
  · exact u19398
  · exact u19399

def b35574 : PairBound 9 := { available := 278, camps := [{ cop := 1, region := 16, targets := 36 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,5)], upper := (rows 35 67 44 140 81 310 342 406 278), lower := (rows 35 67 44 140 81 32 64 128 256), losses := [] }

theorem u35574 : Upper (D 6) (R 6) [34,65,40,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35575 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 44 140 82 309 341 405 277), lower := (rows 35 67 44 140 82 32 64 128 256), losses := [] }

theorem u35575 : Upper (D 6) (R 6) [34,65,40,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35576 : Route 9 := (fun mask => (mask,id))

def c35576 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35576 : Upper (D 6) (R 6) [34,65,40,132,68] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,68] 13 (by decide) (choices 1) [1,2,16,256] r35576 c35576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19400
  · exact u19401
  · exact u19402
  · exact u19403

def r35577 : Route 9 := (fun mask => (mask,id))

def c35577 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35577 : Upper (D 6) (R 6) [34,65,40,132,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,257] 13 (by decide) (choices 1) [2,4,16,64] r35577 c35577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19404
  · exact u19405
  · exact u19406
  · exact u19407

def r35578 : Route 9 := (fun mask => (mask,id))

def c35578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35578 : Upper (D 6) (R 6) [34,65,40,132,258] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,258] 13 (by decide) (choices 1) [1,4,16,64] r35578 c35578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19408
  · exact u19409
  · exact u19410
  · exact u19411

def r35579 : Route 9 := (fun mask => (mask,id))

def c35579 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35579 : Upper (D 6) (R 6) [34,65,40,132,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,260] 13 (by decide) (choices 1) [1,2,16,64] r35579 c35579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19412
  · exact u19413
  · exact u19414
  · exact u19415

#print axioms u35579
end Delivery.IrregularNine14.P06
