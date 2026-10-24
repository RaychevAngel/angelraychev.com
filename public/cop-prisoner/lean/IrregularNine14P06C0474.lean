import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0159
import IrregularNine14P06C0160
import IrregularNine14P06C0161

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28440 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 35 133 56 88 358 326 454 326), lower := (rows 7 35 133 56 88 32 64 128 256), losses := [] }

theorem u28440 : Upper (D 6) (R 6) [6,33,129,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28440
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28441 : Route 9 := (fun mask => (mask,id))

def c28441 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28441 : Upper (D 6) (R 6) [6,33,129,48,258] 13 := by
  apply FastRouting.sound _ _ [6,33,129,48,258] 13 (by decide) (choices 1) [4,8,64] r28441 c28441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9585
  · exact u9586
  · exact u9587

def r28442 : Route 9 := (fun mask => (mask,id))

def c28442 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28442 : Upper (D 6) (R 6) [6,33,129,48,260] 13 := by
  apply FastRouting.sound _ _ [6,33,129,48,260] 13 (by decide) (choices 1) [2,8,64] r28442 c28442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9588
  · exact u9589
  · exact u9590

def b28443 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 376, targets := 1 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 35 133 56 280 102 70 198 326), lower := (rows 7 35 133 56 280 32 64 128 256), losses := [] }

theorem u28443 : Upper (D 6) (R 6) [6,33,129,48,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28443
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28444 : Route 9 := (fun mask => (mask,id))

def c28444 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28444 : Upper (D 6) (R 6) [6,33,129,48,320] 13 := by
  apply FastRouting.sound _ _ [6,33,129,48,320] 13 (by decide) (choices 1) [2,4,8,64] r28444 c28444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9591
  · exact u9592
  · exact u9593
  · exact u9594

def r28445 : Route 9 := (fun mask => (mask,id))

def c28445 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28445 : Upper (D 6) (R 6) [6,33,129,66,68] 13 := by
  apply FastRouting.sound _ _ [6,33,129,66,68] 13 (by decide) (choices 1) [8,16,256] r28445 c28445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9595
  · exact u9596
  · exact u9597

def b28446 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 74 88 308 372 436 308), lower := (rows 7 35 133 74 88 32 64 128 256), losses := [] }

theorem u28446 : Upper (D 6) (R 6) [6,33,129,66,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28446
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28447 : Route 9 := (fun mask => (mask,id))

def c28447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28447 : Upper (D 6) (R 6) [6,33,129,66,96] 13 := by
  apply FastRouting.sound _ _ [6,33,129,66,96] 13 (by decide) (choices 1) [4,8,16,256] r28447 c28447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9598
  · exact u9599
  · exact u9600
  · exact u9601

def r28448 : Route 9 := (fun mask => (mask,id))

def c28448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28448 : Upper (D 6) (R 6) [6,33,129,66,260] 13 := by
  apply FastRouting.sound _ _ [6,33,129,66,260] 13 (by decide) (choices 1) [8,16,64] r28448 c28448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9602
  · exact u9603
  · exact u9604

def r28449 : Route 9 := (fun mask => (mask,id))

def c28449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28449 : Upper (D 6) (R 6) [6,33,129,66,264] 13 := by
  apply FastRouting.sound _ _ [6,33,129,66,264] 13 (by decide) (choices 1) [4,16,64] r28449 c28449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9605
  · exact u9606
  · exact u9607

def r28450 : Route 9 := (fun mask => (mask,id))

def c28450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28450 : Upper (D 6) (R 6) [6,33,129,66,288] 13 := by
  apply FastRouting.sound _ _ [6,33,129,66,288] 13 (by decide) (choices 1) [4,8,16,64] r28450 c28450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9608
  · exact u9609
  · exact u9610
  · exact u9611

def r28451 : Route 9 := (fun mask => (mask,id))

def c28451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28451 : Upper (D 6) (R 6) [6,33,129,66,320] 13 := by
  apply FastRouting.sound _ _ [6,33,129,66,320] 13 (by decide) (choices 1) [4,8,16] r28451 c28451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9612
  · exact u9613
  · exact u9614

def b28452 : PairBound 9 := { available := 306, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 35 133 76 88 306 370 434 306), lower := (rows 7 35 133 76 88 32 64 128 256), losses := [] }

theorem u28452 : Upper (D 6) (R 6) [6,33,129,68,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28452
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28453 : Route 9 := (fun mask => (mask,id))

def c28453 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u28453 : Upper (D 6) (R 6) [6,33,129,68,96] 13 := by
  apply FastRouting.sound _ _ [6,33,129,68,96] 13 (by decide) (choices 1) [2,8,16,256] r28453 c28453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9615
  · exact u9616
  · exact u9617
  · exact u9618

def r28454 : Route 9 := (fun mask => (mask,id))

def c28454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28454 : Upper (D 6) (R 6) [6,33,129,68,258] 13 := by
  apply FastRouting.sound _ _ [6,33,129,68,258] 13 (by decide) (choices 1) [8,16,64] r28454 c28454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9619
  · exact u9620
  · exact u9621

def r28455 : Route 9 := (fun mask => (mask,id))

def c28455 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28455 : Upper (D 6) (R 6) [6,33,129,68,264] 13 := by
  apply FastRouting.sound _ _ [6,33,129,68,264] 13 (by decide) (choices 1) [2,16,64] r28455 c28455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9622
  · exact u9623
  · exact u9624

def r28456 : Route 9 := (fun mask => (mask,id))

def c28456 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28456 : Upper (D 6) (R 6) [6,33,129,68,288] 13 := by
  apply FastRouting.sound _ _ [6,33,129,68,288] 13 (by decide) (choices 1) [2,8,16,64] r28456 c28456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9625
  · exact u9626
  · exact u9627
  · exact u9628

def r28457 : Route 9 := (fun mask => (mask,id))

def c28457 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28457 : Upper (D 6) (R 6) [6,33,129,68,320] 13 := by
  apply FastRouting.sound _ _ [6,33,129,68,320] 13 (by decide) (choices 1) [2,8,16] r28457 c28457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9629
  · exact u9630
  · exact u9631

def b28458 : PairBound 9 := { available := 294, camps := [{ cop := 6, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 133 88 88 294 358 422 294), lower := (rows 7 35 133 88 88 32 64 128 256), losses := [] }

theorem u28458 : Upper (D 6) (R 6) [6,33,129,80,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28458
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28459 : PairBound 9 := { available := 270, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 133 88 112 302 334 398 270), lower := (rows 7 35 133 88 112 32 64 128 256), losses := [] }

theorem u28459 : Upper (D 6) (R 6) [6,33,129,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28459
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28460 : Route 9 := (fun mask => (mask,id))

def c28460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28460 : Upper (D 6) (R 6) [6,33,129,80,258] 13 := by
  apply FastRouting.sound _ _ [6,33,129,80,258] 13 (by decide) (choices 1) [4,8,64] r28460 c28460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9632
  · exact u9633
  · exact u9634

def r28461 : Route 9 := (fun mask => (mask,id))

def c28461 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28461 : Upper (D 6) (R 6) [6,33,129,80,260] 13 := by
  apply FastRouting.sound _ _ [6,33,129,80,260] 13 (by decide) (choices 1) [2,8,64] r28461 c28461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9635
  · exact u9636
  · exact u9637

def r28462 : Route 9 := (fun mask => (mask,id))

def c28462 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28462 : Upper (D 6) (R 6) [6,33,129,80,264] 13 := by
  apply FastRouting.sound _ _ [6,33,129,80,264] 13 (by decide) (choices 1) [2,4,64] r28462 c28462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9638
  · exact u9639
  · exact u9640

def r28463 : Route 9 := (fun mask => (mask,id))

def c28463 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28463 : Upper (D 6) (R 6) [6,33,129,80,288] 13 := by
  apply FastRouting.sound _ _ [6,33,129,80,288] 13 (by decide) (choices 1) [2,4,8,64] r28463 c28463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9641
  · exact u9642
  · exact u9643
  · exact u9644

def b28464 : PairBound 9 := { available := 46, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 35 133 88 336 46 110 174 302), lower := (rows 7 35 133 88 336 32 64 128 256), losses := [] }

theorem u28464 : Upper (D 6) (R 6) [6,33,129,80,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28464
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28465 : Route 9 := (fun mask => (mask,id))

def c28465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28465 : Upper (D 6) (R 6) [6,33,129,96,258] 13 := by
  apply FastRouting.sound _ _ [6,33,129,96,258] 13 (by decide) (choices 1) [4,8,16,64] r28465 c28465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9645
  · exact u9646
  · exact u9647
  · exact u9648

def r28466 : Route 9 := (fun mask => (mask,id))

def c28466 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28466 : Upper (D 6) (R 6) [6,33,129,96,260] 13 := by
  apply FastRouting.sound _ _ [6,33,129,96,260] 13 (by decide) (choices 1) [2,8,16,64] r28466 c28466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9649
  · exact u9650
  · exact u9651
  · exact u9652

def r28467 : Route 9 := (fun mask => (mask,id))

def c28467 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28467 : Upper (D 6) (R 6) [6,33,129,96,264] 13 := by
  apply FastRouting.sound _ _ [6,33,129,96,264] 13 (by decide) (choices 1) [2,4,16,64] r28467 c28467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9653
  · exact u9654
  · exact u9655
  · exact u9656

def r28468 : Route 9 := (fun mask => (mask,id))

def c28468 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28468 : Upper (D 6) (R 6) [6,33,129,96,320] 13 := by
  apply FastRouting.sound _ _ [6,33,129,96,320] 13 (by decide) (choices 1) [2,4,8,16] r28468 c28468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9657
  · exact u9658
  · exact u9659
  · exact u9660

def b28469 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 140 25 22 352 352 480 352), lower := (rows 7 35 140 25 22 32 64 128 256), losses := [] }

theorem u28469 : Upper (D 6) (R 6) [6,33,136,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28469
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28470 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 140 25 50 356 324 452 324), lower := (rows 7 35 140 25 50 32 64 128 256), losses := [] }

theorem u28470 : Upper (D 6) (R 6) [6,33,136,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28470
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28471 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 140 25 52 354 322 450 322), lower := (rows 7 35 140 25 52 32 64 128 256), losses := [] }

theorem u28471 : Upper (D 6) (R 6) [6,33,136,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28471
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28472 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 0, region := 368, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 140 25 82 356 356 484 356), lower := (rows 7 35 140 25 82 32 64 128 256), losses := [] }

theorem u28472 : Upper (D 6) (R 6) [6,33,136,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28472
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28473 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 0, region := 354, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 35 140 25 84 354 354 482 354), lower := (rows 7 35 140 25 84 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 25 35 67 131 259), good := (rows 502 498 156 508 84 32 64 128 256) }] }

theorem u28473 : Upper (D 6) (R 6) [6,33,136,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28473
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28474 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 7 35 140 25 112 358 326 454 326), lower := (rows 7 35 140 25 112 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 33 65 129 257), good := (rows 502 498 156 508 112 32 64 128 256) },{ target := 5, region := (rows 1 2 12 8 16 0 65 129 257), good := (rows 455 451 140 477 80 0 64 128 256) }] }

theorem u28474 : Upper (D 6) (R 6) [6,33,136,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28474
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28475 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 228, targets := 3 },{ cop := 0, region := 368, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 140 25 274 100 100 228 356), lower := (rows 7 35 140 25 274 32 64 128 256), losses := [] }

theorem u28475 : Upper (D 6) (R 6) [6,33,136,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28475
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28476 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 35 140 25 276 98 98 226 354), lower := (rows 7 35 140 25 276 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 25 35 67 131 259), good := (rows 502 498 156 508 276 32 64 128 256) }] }

theorem u28476 : Upper (D 6) (R 6) [6,33,136,17,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28476
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28477 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 7 35 140 25 304 102 70 198 326), lower := (rows 7 35 140 25 304 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 33 65 129 257), good := (rows 502 498 156 508 304 32 64 128 256) },{ target := 5, region := (rows 1 2 12 8 16 0 65 129 257), good := (rows 455 451 140 477 272 0 64 128 256) }] }

theorem u28477 : Upper (D 6) (R 6) [6,33,136,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28477
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28478 : Route 9 := (fun mask => (mask,id))

def c28478 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28478 : Upper (D 6) (R 6) [6,33,136,17,320] 13 := by
  apply FastRouting.sound _ _ [6,33,136,17,320] 13 (by decide) (choices 1) [2,4,64] r28478 c28478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9661
  · exact u9662
  · exact u9663

def b28479 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 140 26 21 352 352 480 352), lower := (rows 7 35 140 26 21 32 64 128 256), losses := [] }

theorem u28479 : Upper (D 6) (R 6) [6,33,136,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28479
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28480 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 140 26 49 356 324 452 324), lower := (rows 7 35 140 26 49 32 64 128 256), losses := [] }

theorem u28480 : Upper (D 6) (R 6) [6,33,136,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28480
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28481 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 11, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 140 26 52 353 321 449 321), lower := (rows 7 35 140 26 52 32 64 128 256), losses := [] }

theorem u28481 : Upper (D 6) (R 6) [6,33,136,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28481
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28482 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 0, region := 368, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 35 140 26 81 356 356 484 356), lower := (rows 7 35 140 26 81 32 64 128 256), losses := [] }

theorem u28482 : Upper (D 6) (R 6) [6,33,136,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28482
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28483 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 368, targets := 2 },{ cop := 0, region := 354, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 35 140 26 84 353 353 481 353), lower := (rows 7 35 140 26 84 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 35 67 131 259), good := (rows 501 497 156 508 84 32 64 128 256) }] }

theorem u28483 : Upper (D 6) (R 6) [6,33,136,18,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28483
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28484 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 453, targets := 32 },{ cop := 0, region := 368, targets := 2 }], pairs := [(0,5),(2,5),(4,1)], upper := (rows 7 35 140 26 112 357 325 453 325), lower := (rows 7 35 140 26 112 32 64 128 256), losses := [] }

theorem u28484 : Upper (D 6) (R 6) [6,33,136,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28484
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28485 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 228, targets := 3 },{ cop := 0, region := 368, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 35 140 26 273 100 100 228 356), lower := (rows 7 35 140 26 273 32 64 128 256), losses := [] }

theorem u28485 : Upper (D 6) (R 6) [6,33,136,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28485
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28486 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 2 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 35 140 26 276 97 97 225 353), lower := (rows 7 35 140 26 276 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 35 67 131 259), good := (rows 501 497 156 508 276 32 64 128 256) }] }

theorem u28486 : Upper (D 6) (R 6) [6,33,136,18,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28486
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28487 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 197, targets := 32 },{ cop := 0, region := 368, targets := 2 }], pairs := [(0,5),(2,5),(4,1)], upper := (rows 7 35 140 26 304 101 69 197 325), lower := (rows 7 35 140 26 304 32 64 128 256), losses := [] }

theorem u28487 : Upper (D 6) (R 6) [6,33,136,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28487
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28488 : Route 9 := (fun mask => (mask,id))

def c28488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28488 : Upper (D 6) (R 6) [6,33,136,18,320] 13 := by
  apply FastRouting.sound _ _ [6,33,136,18,320] 13 (by decide) (choices 1) [1,4,64] r28488 c28488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9664
  · exact u9665
  · exact u9666

def b28489 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 24, targets := 96 }], pairs := [(3,5),(3,6),(4,5)], upper := (rows 7 35 140 28 19 352 352 480 352), lower := (rows 7 35 140 28 19 32 64 128 256), losses := [] }

theorem u28489 : Upper (D 6) (R 6) [6,33,136,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28489
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28490 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 370, targets := 4 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,2),(4,1),(4,2)], upper := (rows 7 35 140 28 49 354 322 450 322), lower := (rows 7 35 140 28 49 32 64 128 256), losses := [] }

theorem u28490 : Upper (D 6) (R 6) [6,33,136,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28490
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28491 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 140 28 50 353 321 449 321), lower := (rows 7 35 140 28 50 32 64 128 256), losses := [] }

theorem u28491 : Upper (D 6) (R 6) [6,33,136,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28491
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28492 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(2,0),(4,2)], upper := (rows 7 35 140 28 81 354 354 482 354), lower := (rows 7 35 140 28 81 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 486 482 140 28 508 32 64 128 256) }] }

theorem u28492 : Upper (D 6) (R 6) [6,33,136,20,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28492
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28493 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 7 35 140 28 82 353 353 481 353), lower := (rows 7 35 140 28 82 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 485 481 140 28 508 32 64 128 256) }] }

theorem u28493 : Upper (D 6) (R 6) [6,33,136,20,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28493
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28494 : Route 9 := (fun mask => (mask,id))

def c28494 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u28494 : Upper (D 6) (R 6) [6,33,136,20,96] 13 := by
  apply FastRouting.sound _ _ [6,33,136,20,96] 13 (by decide) (choices 1) [1,2,64,256] r28494 c28494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9667
  · exact u9668
  · exact u9669
  · exact u9670

def b28495 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(2,0),(4,2)], upper := (rows 7 35 140 28 273 98 98 226 354), lower := (rows 7 35 140 28 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 67 131 259), good := (rows 486 482 140 28 508 32 64 128 256) }] }

theorem u28495 : Upper (D 6) (R 6) [6,33,136,20,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28495
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28496 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 7 35 140 28 274 97 97 225 353), lower := (rows 7 35 140 28 274 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 485 481 140 28 508 32 64 128 256) }] }

theorem u28496 : Upper (D 6) (R 6) [6,33,136,20,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28496
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28497 : Route 9 := (fun mask => (mask,id))

def c28497 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28497 : Upper (D 6) (R 6) [6,33,136,20,288] 13 := by
  apply FastRouting.sound _ _ [6,33,136,20,288] 13 (by decide) (choices 1) [1,2,64] r28497 c28497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9671
  · exact u9672
  · exact u9673

def r28498 : Route 9 := (fun mask => (mask,id))

def c28498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28498 : Upper (D 6) (R 6) [6,33,136,20,320] 13 := by
  apply FastRouting.sound _ _ [6,33,136,20,320] 13 (by decide) (choices 1) [1,2,64] r28498 c28498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9674
  · exact u9675
  · exact u9676

def b28499 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 7 35 140 56 19 356 324 452 324), lower := (rows 7 35 140 56 19 32 64 128 256), losses := [] }

theorem u28499 : Upper (D 6) (R 6) [6,33,136,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b28499
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28499
end Delivery.IrregularNine14.P06
