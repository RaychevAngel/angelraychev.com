import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0323
import IrregularNine14P06C0324
import IrregularNine14P06C0325

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35580 : Route 9 := (fun mask => (mask,id))

def c35580 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35580 : Upper (D 6) (R 6) [34,65,40,132,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,132,320] 13 (by decide) (choices 1) [1,2,4,16] r35580 c35580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19416
  · exact u19417
  · exact u19418
  · exact u19419

def b35581 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 44 152 19 356 324 452 324), lower := (rows 35 67 44 152 19 32 64 128 256), losses := [] }

theorem u35581 : Upper (D 6) (R 6) [34,65,40,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35582 : Route 9 := (fun mask => (mask,id))

def c35582 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35582 : Upper (D 6) (R 6) [34,65,40,144,5] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,5] 13 (by decide) (choices 1) [2,4,64,256] r35582 c35582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19420
  · exact u19421
  · exact u19422
  · exact u19423

def r35583 : Route 9 := (fun mask => (mask,id))

def c35583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35583 : Upper (D 6) (R 6) [34,65,40,144,6] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,6] 13 (by decide) (choices 1) [1,4,64,256] r35583 c35583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19424
  · exact u19425
  · exact u19426
  · exact u19427

def b35584 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 16, targets := 36 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,5)], upper := (rows 35 67 44 152 81 294 326 390 262), lower := (rows 35 67 44 152 81 32 64 128 256), losses := [] }

theorem u35584 : Upper (D 6) (R 6) [34,65,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35585 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 44 152 82 293 325 389 261), lower := (rows 35 67 44 152 82 32 64 128 256), losses := [] }

theorem u35585 : Upper (D 6) (R 6) [34,65,40,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35586 : Route 9 := (fun mask => (mask,id))

def c35586 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35586 : Upper (D 6) (R 6) [34,65,40,144,68] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,68] 13 (by decide) (choices 1) [1,2,4,256] r35586 c35586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19428
  · exact u19429
  · exact u19430
  · exact u19431

def r35587 : Route 9 := (fun mask => (mask,id))

def c35587 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35587 : Upper (D 6) (R 6) [34,65,40,144,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,257] 13 (by decide) (choices 1) [2,4,64] r35587 c35587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19432
  · exact u19433
  · exact u19434

def r35588 : Route 9 := (fun mask => (mask,id))

def c35588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35588 : Upper (D 6) (R 6) [34,65,40,144,258] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,258] 13 (by decide) (choices 1) [1,4,64] r35588 c35588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19435
  · exact u19436
  · exact u19437

def r35589 : Route 9 := (fun mask => (mask,id))

def c35589 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35589 : Upper (D 6) (R 6) [34,65,40,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,260] 13 (by decide) (choices 1) [1,2,4,64] r35589 c35589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19438
  · exact u19439
  · exact u19440
  · exact u19441

def r35590 : Route 9 := (fun mask => (mask,id))

def c35590 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35590 : Upper (D 6) (R 6) [34,65,40,144,320] 13 := by
  apply FastRouting.sound _ _ [34,65,40,144,320] 13 (by decide) (choices 1) [1,2,4] r35590 c35590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19442
  · exact u19443
  · exact u19444

def b35591 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 44 200 19 308 340 404 276), lower := (rows 35 67 44 200 19 32 64 128 256), losses := [] }

theorem u35591 : Upper (D 6) (R 6) [34,65,40,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35592 : Route 9 := (fun mask => (mask,id))

def c35592 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35592 : Upper (D 6) (R 6) [34,65,40,192,5] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,5] 13 (by decide) (choices 1) [2,4,16,256] r35592 c35592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19445
  · exact u19446
  · exact u19447
  · exact u19448

def r35593 : Route 9 := (fun mask => (mask,id))

def c35593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35593 : Upper (D 6) (R 6) [34,65,40,192,6] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,6] 13 (by decide) (choices 1) [1,4,16,256] r35593 c35593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19449
  · exact u19450
  · exact u19451
  · exact u19452

def r35594 : Route 9 := (fun mask => (mask,id))

def c35594 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35594 : Upper (D 6) (R 6) [34,65,40,192,257] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,257] 13 (by decide) (choices 1) [2,4,16] r35594 c35594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19453
  · exact u19454
  · exact u19455

def r35595 : Route 9 := (fun mask => (mask,id))

def c35595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35595 : Upper (D 6) (R 6) [34,65,40,192,258] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,258] 13 (by decide) (choices 1) [1,4,16] r35595 c35595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19456
  · exact u19457
  · exact u19458

def r35596 : Route 9 := (fun mask => (mask,id))

def c35596 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35596 : Upper (D 6) (R 6) [34,65,40,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,260] 13 (by decide) (choices 1) [1,2,4,16] r35596 c35596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19459
  · exact u19460
  · exact u19461
  · exact u19462

def b35597 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 492, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 44 392 19 116 84 212 340), lower := (rows 35 67 44 392 19 32 64 128 256), losses := [] }

theorem u35597 : Upper (D 6) (R 6) [34,65,40,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35598 : Route 9 := (fun mask => (mask,id))

def c35598 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35598 : Upper (D 6) (R 6) [34,65,40,384,5] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,5] 13 (by decide) (choices 1) [2,4,16,64] r35598 c35598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19463
  · exact u19464
  · exact u19465
  · exact u19466

def r35599 : Route 9 := (fun mask => (mask,id))

def c35599 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35599 : Upper (D 6) (R 6) [34,65,40,384,6] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,6] 13 (by decide) (choices 1) [1,4,16,64] r35599 c35599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19467
  · exact u19468
  · exact u19469
  · exact u19470

def b35600 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 16, targets := 36 },{ cop := 4, region := 2, targets := 4 }], pairs := [(1,2),(4,2),(4,5)], upper := (rows 35 67 44 392 81 54 86 150 278), lower := (rows 35 67 44 392 81 32 64 128 256), losses := [] }

theorem u35600 : Upper (D 6) (R 6) [34,65,40,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35601 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 67 44 392 82 53 85 149 277), lower := (rows 35 67 44 392 82 32 64 128 256), losses := [] }

theorem u35601 : Upper (D 6) (R 6) [34,65,40,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35602 : Route 9 := (fun mask => (mask,id))

def c35602 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35602 : Upper (D 6) (R 6) [34,65,40,384,68] 13 := by
  apply FastRouting.sound _ _ [34,65,40,384,68] 13 (by decide) (choices 1) [1,2,4,16] r35602 c35602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19471
  · exact u19472
  · exact u19473
  · exact u19474

def b35603 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 100 11 28 436 468 404 404), lower := (rows 35 67 100 11 28 32 64 128 256), losses := [] }

theorem u35603 : Upper (D 6) (R 6) [34,65,96,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35604 : PairBound 9 := { available := 284, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 100 11 148 316 348 412 284), lower := (rows 35 67 100 11 148 32 64 128 256), losses := [] }

theorem u35604 : Upper (D 6) (R 6) [34,65,96,3,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35605 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 100 11 152 308 340 404 276), lower := (rows 35 67 100 11 152 32 64 128 256), losses := [] }

theorem u35605 : Upper (D 6) (R 6) [34,65,96,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35606 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 500, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 67 100 11 400 60 92 156 284), lower := (rows 35 67 100 11 400 32 64 128 256), losses := [] }

theorem u35606 : Upper (D 6) (R 6) [34,65,96,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35607 : PairBound 9 := { available := 404, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 3, region := 466, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 67 100 13 26 436 468 404 404), lower := (rows 35 67 100 13 26 32 64 128 256), losses := [] }

theorem u35607 : Upper (D 6) (R 6) [34,65,96,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35608 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 100 13 28 434 466 402 402), lower := (rows 35 67 100 13 28 32 64 128 256), losses := [] }

theorem u35608 : Upper (D 6) (R 6) [34,65,96,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35609 : PairBound 9 := { available := 284, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 3, region := 466, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 67 100 13 146 316 348 412 284), lower := (rows 35 67 100 13 146 32 64 128 256), losses := [] }

theorem u35609 : Upper (D 6) (R 6) [34,65,96,5,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35610 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 3, region := 466, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 67 100 13 148 314 346 410 282), lower := (rows 35 67 100 13 148 32 64 128 256), losses := [] }

theorem u35610 : Upper (D 6) (R 6) [34,65,96,5,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35611 : PairBound 9 := { available := 278, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 3, region := 466, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 67 100 13 152 310 342 406 278), lower := (rows 35 67 100 13 152 32 64 128 256), losses := [] }

theorem u35611 : Upper (D 6) (R 6) [34,65,96,5,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35612 : PairBound 9 := { available := 30, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 3, region := 466, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 67 100 13 400 62 94 158 286), lower := (rows 35 67 100 13 400 32 64 128 256), losses := [] }

theorem u35612 : Upper (D 6) (R 6) [34,65,96,5,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35613 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 67 100 25 26 420 452 388 388), lower := (rows 35 67 100 25 26 32 64 128 256), losses := [] }

theorem u35613 : Upper (D 6) (R 6) [34,65,96,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35614 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 0, region := 452, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 100 25 28 422 454 390 390), lower := (rows 35 67 100 25 28 32 64 128 256), losses := [] }

theorem u35614 : Upper (D 6) (R 6) [34,65,96,17,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35615 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 3, region := 356, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 100 25 146 300 332 396 268), lower := (rows 35 67 100 25 146 32 64 128 256), losses := [] }

theorem u35615 : Upper (D 6) (R 6) [34,65,96,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35616 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 3, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 67 100 25 148 302 334 398 270), lower := (rows 35 67 100 25 148 32 64 128 256), losses := [{ target := 2, region := (rows 5 6 0 24 16 32 64 128 256), good := (rows 35 67 99 25 155 32 64 128 256) }] }

theorem u35616 : Upper (D 6) (R 6) [34,65,96,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35617 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 0, region := 324, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 100 25 152 294 326 390 262), lower := (rows 35 67 100 25 152 32 64 128 256), losses := [] }

theorem u35617 : Upper (D 6) (R 6) [34,65,96,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35618 : Route 9 := (fun mask => (mask,id))

def c35618 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35618 : Upper (D 6) (R 6) [34,65,96,17,384] 13 := by
  apply FastRouting.sound _ _ [34,65,96,17,384] 13 (by decide) (choices 1) [2,4,8] r35618 c35618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19475
  · exact u19476
  · exact u19477

def b35619 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 100 28 28 419 451 387 387), lower := (rows 35 67 100 28 28 32 64 128 256), losses := [] }

theorem u35619 : Upper (D 6) (R 6) [34,65,96,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35620 : Route 9 := (fun mask => (mask,id))

def c35620 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35620 : Upper (D 6) (R 6) [34,65,96,20,129] 13 := by
  apply FastRouting.sound _ _ [34,65,96,20,129] 13 (by decide) (choices 1) [2,4,8,256] r35620 c35620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19478
  · exact u19479
  · exact u19480
  · exact u19481

def b35621 : PairBound 9 := { available := 267, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 100 28 148 299 331 395 267), lower := (rows 35 67 100 28 148 32 64 128 256), losses := [] }

theorem u35621 : Upper (D 6) (R 6) [34,65,96,20,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35622 : Route 9 := (fun mask => (mask,id))

def c35622 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35622 : Upper (D 6) (R 6) [34,65,96,20,136] 13 := by
  apply FastRouting.sound _ _ [34,65,96,20,136] 13 (by decide) (choices 1) [1,2,4,256] r35622 c35622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19482
  · exact u19483
  · exact u19484
  · exact u19485

def r35623 : Route 9 := (fun mask => (mask,id))

def c35623 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35623 : Upper (D 6) (R 6) [34,65,96,20,384] 13 := by
  apply FastRouting.sound _ _ [34,65,96,20,384] 13 (by decide) (choices 1) [1,2,4,8] r35623 c35623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19486
  · exact u19487
  · exact u19488
  · exact u19489

def r35624 : Route 9 := (fun mask => (mask,id))

def c35624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35624 : Upper (D 6) (R 6) [34,65,96,129,258] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,258] 13 (by decide) (choices 1) [4,8,16] r35624 c35624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19490
  · exact u19491
  · exact u19492

def r35625 : Route 9 := (fun mask => (mask,id))

def c35625 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35625 : Upper (D 6) (R 6) [34,65,96,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,260] 13 (by decide) (choices 1) [2,4,8,16] r35625 c35625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19493
  · exact u19494
  · exact u19495
  · exact u19496

def r35626 : Route 9 := (fun mask => (mask,id))

def c35626 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35626 : Upper (D 6) (R 6) [34,65,96,129,264] 13 := by
  apply FastRouting.sound _ _ [34,65,96,129,264] 13 (by decide) (choices 1) [2,4,16] r35626 c35626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19497
  · exact u19498
  · exact u19499

theorem m35627_16 : Upper (D 6) (R 6) [34,65,96,132,260,16] 13 :=
  permutation_upper _ _ _ [34,65,96,132,260,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19502

def r35627 : Route 9 := (fun mask => (mask,id))

def c35627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35627 : Upper (D 6) (R 6) [34,65,96,132,260] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132,260] 13 (by decide) (choices 1) [1,2,8,16] r35627 c35627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19500
  · exact u19501
  · exact u19502
  · exact m35627_16

def r35628 : Route 9 := (fun mask => (mask,id))

def c35628 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35628 : Upper (D 6) (R 6) [34,65,96,132,264] 13 := by
  apply FastRouting.sound _ _ [34,65,96,132,264] 13 (by decide) (choices 1) [1,2,4,16] r35628 c35628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19503
  · exact u19504
  · exact u19505
  · exact u19506

def r35629 : Route 9 := (fun mask => (mask,id))

def c35629 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35629 : Upper (D 6) (R 6) [34,65,96,144,264] 13 := by
  apply FastRouting.sound _ _ [34,65,96,144,264] 13 (by decide) (choices 1) [1,2,4] r35629 c35629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19507
  · exact u19508
  · exact u19509

def b35630 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 16, targets := 3 },{ cop := 3, region := 16, targets := 32 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 67 133 14 28 368 368 496 368), lower := (rows 35 67 133 14 28 32 64 128 256), losses := [] }

theorem u35630 : Upper (D 6) (R 6) [34,65,129,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35631 : Route 9 := (fun mask => (mask,id))

def c35631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u35631 : Upper (D 6) (R 6) [34,65,129,6,36] 13 := by
  apply FastRouting.sound _ _ [34,65,129,6,36] 13 (by decide) (choices 1) [8,16,64,256] r35631 c35631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19510
  · exact u19511
  · exact u19512
  · exact u19513

def r35632 : Route 9 := (fun mask => (mask,id))

def c35632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u35632 : Upper (D 6) (R 6) [34,65,129,6,40] 13 := by
  apply FastRouting.sound _ _ [34,65,129,6,40] 13 (by decide) (choices 1) [4,16,64,256] r35632 c35632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19514
  · exact u19515
  · exact u19516
  · exact u19517

def r35633 : Route 9 := (fun mask => (mask,id))

def c35633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35633 : Upper (D 6) (R 6) [34,65,129,6,68] 13 := by
  apply FastRouting.sound _ _ [34,65,129,6,68] 13 (by decide) (choices 1) [8,16,256] r35633 c35633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19518
  · exact u19519
  · exact u19520

def r35634 : Route 9 := (fun mask => (mask,id))

def c35634 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35634 : Upper (D 6) (R 6) [34,65,129,6,72] 13 := by
  apply FastRouting.sound _ _ [34,65,129,6,72] 13 (by decide) (choices 1) [4,16,256] r35634 c35634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19521
  · exact u19522
  · exact u19523

def b35635 : PairBound 9 := { available := 284, camps := [{ cop := 3, region := 368, targets := 3 },{ cop := 4, region := 3, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 67 133 14 112 316 348 412 284), lower := (rows 35 67 133 14 112 32 64 128 256), losses := [] }

theorem u35635 : Upper (D 6) (R 6) [34,65,129,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35636 : Route 9 := (fun mask => (mask,id))

def c35636 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35636 : Upper (D 6) (R 6) [34,65,129,6,260] 13 := by
  apply FastRouting.sound _ _ [34,65,129,6,260] 13 (by decide) (choices 1) [8,16,64] r35636 c35636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19524
  · exact u19525
  · exact u19526

def r35637 : Route 9 := (fun mask => (mask,id))

def c35637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35637 : Upper (D 6) (R 6) [34,65,129,6,264] 13 := by
  apply FastRouting.sound _ _ [34,65,129,6,264] 13 (by decide) (choices 1) [4,16,64] r35637 c35637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19527
  · exact u19528
  · exact u19529

def r35638 : Route 9 := (fun mask => (mask,id))

def c35638 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35638 : Upper (D 6) (R 6) [34,65,129,6,288] 13 := by
  apply FastRouting.sound _ _ [34,65,129,6,288] 13 (by decide) (choices 1) [4,8,16,64] r35638 c35638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19530
  · exact u19531
  · exact u19532
  · exact u19533

def r35639 : Route 9 := (fun mask => (mask,id))

def c35639 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35639 : Upper (D 6) (R 6) [34,65,129,6,320] 13 := by
  apply FastRouting.sound _ _ [34,65,129,6,320] 13 (by decide) (choices 1) [4,8,16] r35639 c35639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19534
  · exact u19535
  · exact u19536

#print axioms u35639
end Delivery.IrregularNine14.P06
