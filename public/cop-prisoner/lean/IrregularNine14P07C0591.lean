import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0342
import IrregularNine14P07C0343
import IrregularNine14P07C0344

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35460 : PairBound 9 := { available := 23, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 44 265 208 55 87 151 279), lower := (rows 35 194 44 265 208 32 64 128 256), losses := [] }

theorem u35460 : Upper (D 7) (R 7) [34,192,40,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35461 : Route 9 := (fun mask => (mask,id))

def c35461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35461 : Upper (D 7) (R 7) [34,192,40,258,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,258,65] 13 (by decide) (choices 1) [1,4,16,128] r35461 c35461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20560
  · exact u20561
  · exact u20562
  · exact u20563

def r35462 : Route 9 := (fun mask => (mask,id))

def c35462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35462 : Upper (D 7) (R 7) [34,192,40,258,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,258,68] 13 (by decide) (choices 1) [1,16,128] r35462 c35462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20564
  · exact u20565
  · exact u20566

def b35463 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 44 266 208 53 85 149 277), lower := (rows 35 194 44 266 208 32 64 128 256), losses := [] }

theorem u35463 : Upper (D 7) (R 7) [34,192,40,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35464 : Route 9 := (fun mask => (mask,id))

def c35464 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35464 : Upper (D 7) (R 7) [34,192,40,260,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,260,65] 13 (by decide) (choices 1) [1,2,16,128] r35464 c35464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20567
  · exact u20568
  · exact u20569
  · exact u20570

def b35465 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 194 44 268 82 177 209 145 401), lower := (rows 35 194 44 268 82 32 64 128 256), losses := [] }

theorem u35465 : Upper (D 7) (R 7) [34,192,40,260,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35466 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 1, region := 16, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,5),(4,0),(4,1),(4,5)], upper := (rows 35 194 44 268 208 51 83 147 275), lower := (rows 35 194 44 268 208 32 64 128 256), losses := [] }

theorem u35466 : Upper (D 7) (R 7) [34,192,40,260,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35467 : Route 9 := (fun mask => (mask,id))

def c35467 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35467 : Upper (D 7) (R 7) [34,192,40,272,65] 13 := by
  apply FastRouting.sound _ _ [34,192,40,272,65] 13 (by decide) (choices 1) [1,2,4,128] r35467 c35467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20571
  · exact u20572
  · exact u20573
  · exact u20574

def b35468 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 194 44 280 82 165 197 133 389), lower := (rows 35 194 44 280 82 32 64 128 256), losses := [] }

theorem u35468 : Upper (D 7) (R 7) [34,192,40,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35469 : Route 9 := (fun mask => (mask,id))

def c35469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35469 : Upper (D 7) (R 7) [34,192,40,272,68] 13 := by
  apply FastRouting.sound _ _ [34,192,40,272,68] 13 (by decide) (choices 1) [1,2,128] r35469 c35469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20575
  · exact u20576
  · exact u20577

def b35470 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 33 },{ cop := 4, region := 2, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 44 280 208 39 71 135 263), lower := (rows 35 194 44 280 208 32 64 128 256), losses := [] }

theorem u35470 : Upper (D 7) (R 7) [34,192,40,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35471 : Route 9 := (fun mask => (mask,id))

def c35471 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35471 : Upper (D 7) (R 7) [34,192,40,320,129] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,129] 13 (by decide) (choices 1) [1,2,4,16] r35471 c35471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20578
  · exact u20579
  · exact u20580
  · exact u20581

def b35472 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 16, targets := 97 },{ cop := 4, region := 365, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,6)], upper := (rows 35 194 44 328 146 53 85 149 277), lower := (rows 35 194 44 328 146 32 64 128 256), losses := [] }

theorem u35472 : Upper (D 7) (R 7) [34,192,40,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35473 : Route 9 := (fun mask => (mask,id))

def c35473 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35473 : Upper (D 7) (R 7) [34,192,40,320,132] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,132] 13 (by decide) (choices 1) [1,2,16] r35473 c35473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20582
  · exact u20583
  · exact u20584

theorem m35474_8 : Upper (D 7) (R 7) [34,192,65,129,258,8] 13 :=
  permutation_upper _ _ _ [34,192,65,129,258,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20585

def r35474 : Route 9 := (fun mask => (mask,id))

def c35474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35474 : Upper (D 7) (R 7) [34,192,65,129,258] 13 := by
  apply FastRouting.sound _ _ [34,192,65,129,258] 13 (by decide) (choices 1) [4,8,16] r35474 c35474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20585
  · exact m35474_8
  · exact u20586

def r35475 : Route 9 := (fun mask => (mask,id))

def c35475 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35475 : Upper (D 7) (R 7) [34,192,65,129,260] 13 := by
  apply FastRouting.sound _ _ [34,192,65,129,260] 13 (by decide) (choices 1) [2,8,16] r35475 c35475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20587
  · exact u20588
  · exact u20589

theorem m35476_8 : Upper (D 7) (R 7) [34,192,65,129,288,8] 13 :=
  permutation_upper _ _ _ [34,192,65,129,288,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u20591

def r35476 : Route 9 := (fun mask => (mask,id))

def c35476 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35476 : Upper (D 7) (R 7) [34,192,65,129,288] 13 := by
  apply FastRouting.sound _ _ [34,192,65,129,288] 13 (by decide) (choices 1) [2,4,8,16] r35476 c35476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20590
  · exact u20591
  · exact m35476_8
  · exact u20592

def b35477 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 35 194 69 138 273 60 124 188 316), lower := (rows 35 194 69 138 273 32 64 128 256), losses := [] }

theorem u35477 : Upper (D 7) (R 7) [34,192,65,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35478 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 35 194 69 138 276 57 121 185 313), lower := (rows 35 194 69 138 276 32 64 128 256), losses := [] }

theorem u35478 : Upper (D 7) (R 7) [34,192,65,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35479 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 35 194 69 138 280 53 117 181 309), lower := (rows 35 194 69 138 280 32 64 128 256), losses := [] }

theorem u35479 : Upper (D 7) (R 7) [34,192,65,130,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35480 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 8, targets := 97 },{ cop := 3, region := 373, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6)], upper := (rows 35 194 69 138 304 61 93 157 285), lower := (rows 35 194 69 138 304 32 64 128 256), losses := [] }

theorem u35480 : Upper (D 7) (R 7) [34,192,65,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35481 : Route 9 := (fun mask => (mask,id))

def c35481 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35481 : Upper (D 7) (R 7) [34,192,65,132,257] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,257] 13 (by decide) (choices 1) [2,8,16] r35481 c35481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20593
  · exact u20594
  · exact u20595

def r35482 : Route 9 := (fun mask => (mask,id))

def c35482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35482 : Upper (D 7) (R 7) [34,192,65,132,258] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,258] 13 (by decide) (choices 1) [1,8,16] r35482 c35482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20596
  · exact u20597
  · exact u20598

def r35483 : Route 9 := (fun mask => (mask,id))

def c35483 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35483 : Upper (D 7) (R 7) [34,192,65,132,264] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,264] 13 (by decide) (choices 1) [1,2,16] r35483 c35483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20599
  · exact u20600
  · exact u20601

def r35484 : Route 9 := (fun mask => (mask,id))

def c35484 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35484 : Upper (D 7) (R 7) [34,192,65,132,288] 13 := by
  apply FastRouting.sound _ _ [34,192,65,132,288] 13 (by decide) (choices 1) [1,2,8,16] r35484 c35484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20602
  · exact u20603
  · exact u20604
  · exact u20605

def r35485 : Route 9 := (fun mask => (mask,id))

def c35485 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35485 : Upper (D 7) (R 7) [34,192,65,144,257] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,257] 13 (by decide) (choices 1) [2,4,8] r35485 c35485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20606
  · exact u20607
  · exact u20608

def r35486 : Route 9 := (fun mask => (mask,id))

def c35486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35486 : Upper (D 7) (R 7) [34,192,65,144,258] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,258] 13 (by decide) (choices 1) [1,4,8] r35486 c35486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20609
  · exact u20610
  · exact u20611

def r35487 : Route 9 := (fun mask => (mask,id))

def c35487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35487 : Upper (D 7) (R 7) [34,192,65,144,260] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,260] 13 (by decide) (choices 1) [1,2,8] r35487 c35487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20612
  · exact u20613
  · exact u20614

def r35488 : Route 9 := (fun mask => (mask,id))

def c35488 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35488 : Upper (D 7) (R 7) [34,192,65,144,264] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,264] 13 (by decide) (choices 1) [1,2,4] r35488 c35488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20615
  · exact u20616
  · exact u20617

def r35489 : Route 9 := (fun mask => (mask,id))

def c35489 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35489 : Upper (D 7) (R 7) [34,192,65,144,288] 13 := by
  apply FastRouting.sound _ _ [34,192,65,144,288] 13 (by decide) (choices 1) [1,2,4,8] r35489 c35489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20618
  · exact u20619
  · exact u20620
  · exact u20621

def r35490 : Route 9 := (fun mask => (mask,id))

def c35490 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35490 : Upper (D 7) (R 7) [34,192,65,160,257] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,257] 13 (by decide) (choices 1) [2,4,8,16] r35490 c35490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20622
  · exact u20623
  · exact u20624
  · exact u20625

def r35491 : Route 9 := (fun mask => (mask,id))

def c35491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35491 : Upper (D 7) (R 7) [34,192,65,160,258] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,258] 13 (by decide) (choices 1) [1,4,8,16] r35491 c35491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20626
  · exact u20627
  · exact u20628
  · exact u20629

def r35492 : Route 9 := (fun mask => (mask,id))

def c35492 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35492 : Upper (D 7) (R 7) [34,192,65,160,260] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,260] 13 (by decide) (choices 1) [1,2,8,16] r35492 c35492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20630
  · exact u20631
  · exact u20632
  · exact u20633

def r35493 : Route 9 := (fun mask => (mask,id))

def c35493 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35493 : Upper (D 7) (R 7) [34,192,65,160,264] 13 := by
  apply FastRouting.sound _ _ [34,192,65,160,264] 13 (by decide) (choices 1) [1,2,4,16] r35493 c35493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20634
  · exact u20635
  · exact u20636
  · exact u20637

def b35494 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 70 140 273 57 121 185 313), lower := (rows 35 194 70 140 273 32 64 128 256), losses := [] }

theorem u35494 : Upper (D 7) (R 7) [34,192,66,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35495 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 70 140 280 49 113 177 305), lower := (rows 35 194 70 140 280 32 64 128 256), losses := [] }

theorem u35495 : Upper (D 7) (R 7) [34,192,66,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35496 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 70 140 304 57 89 153 281), lower := (rows 35 194 70 140 304 32 64 128 256), losses := [] }

theorem u35496 : Upper (D 7) (R 7) [34,192,66,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35497 : PairBound 9 := { available := 45, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 441, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 35 194 70 152 273 45 109 173 301), lower := (rows 35 194 70 152 273 32 64 128 256), losses := [] }

theorem u35497 : Upper (D 7) (R 7) [34,192,66,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35498 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 441, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 35 194 70 152 276 41 105 169 297), lower := (rows 35 194 70 152 276 32 64 128 256), losses := [] }

theorem u35498 : Upper (D 7) (R 7) [34,192,66,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35499 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 441, targets := 64 },{ cop := 1, region := 4, targets := 1 }], pairs := [(0,6),(2,0),(3,6),(4,6)], upper := (rows 35 194 70 152 280 37 101 165 293), lower := (rows 35 194 70 152 280 32 64 128 256), losses := [] }

theorem u35499 : Upper (D 7) (R 7) [34,192,66,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35500 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 441, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 35 194 70 152 304 45 77 141 269), lower := (rows 35 194 70 152 304 32 64 128 256), losses := [] }

theorem u35500 : Upper (D 7) (R 7) [34,192,66,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35501 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 441, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 35 194 70 168 273 61 93 157 285), lower := (rows 35 194 70 168 273 32 64 128 256), losses := [] }

theorem u35501 : Upper (D 7) (R 7) [34,192,66,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35502 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 441, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 35 194 70 168 276 57 89 153 281), lower := (rows 35 194 70 168 276 32 64 128 256), losses := [] }

theorem u35502 : Upper (D 7) (R 7) [34,192,66,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35503 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 4, targets := 161 },{ cop := 2, region := 441, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7)], upper := (rows 35 194 70 168 280 53 85 149 277), lower := (rows 35 194 70 168 280 32 64 128 256), losses := [] }

theorem u35503 : Upper (D 7) (R 7) [34,192,66,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35504 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 76 140 273 51 115 179 307), lower := (rows 35 194 76 140 273 32 64 128 256), losses := [] }

theorem u35504 : Upper (D 7) (R 7) [34,192,72,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35505 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 76 140 274 49 113 177 305), lower := (rows 35 194 76 140 274 32 64 128 256), losses := [] }

theorem u35505 : Upper (D 7) (R 7) [34,192,72,132,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35506 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 12, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 76 140 304 51 83 147 275), lower := (rows 35 194 76 140 304 32 64 128 256), losses := [] }

theorem u35506 : Upper (D 7) (R 7) [34,192,72,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35507 : Route 9 := (fun mask => (mask,id))

def c35507 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35507 : Upper (D 7) (R 7) [34,192,72,144,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,257] 13 (by decide) (choices 1) [1,2,4] r35507 c35507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20638
  · exact u20639
  · exact u20640

def r35508 : Route 9 := (fun mask => (mask,id))

def c35508 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35508 : Upper (D 7) (R 7) [34,192,72,144,258] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,258] 13 (by decide) (choices 1) [1,4] r35508 c35508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20641
  · exact u20642

def r35509 : Route 9 := (fun mask => (mask,id))

def c35509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35509 : Upper (D 7) (R 7) [34,192,72,144,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,260] 13 (by decide) (choices 1) [1,2] r35509 c35509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20643
  · exact u20644

def r35510 : Route 9 := (fun mask => (mask,id))

def c35510 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35510 : Upper (D 7) (R 7) [34,192,72,144,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,288] 13 (by decide) (choices 1) [1,2,4] r35510 c35510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20645
  · exact u20646
  · exact u20647

def r35511 : Route 9 := (fun mask => (mask,id))

def c35511 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35511 : Upper (D 7) (R 7) [34,192,72,160,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257] 13 (by decide) (choices 1) [1,2,4,16] r35511 c35511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20648
  · exact u20649
  · exact u20650
  · exact u20651

def r35512 : Route 9 := (fun mask => (mask,id))

def c35512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35512 : Upper (D 7) (R 7) [34,192,72,160,258] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,258] 13 (by decide) (choices 1) [1,4,16] r35512 c35512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20652
  · exact u20653
  · exact u20654

def r35513 : Route 9 := (fun mask => (mask,id))

def c35513 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35513 : Upper (D 7) (R 7) [34,192,72,160,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,260] 13 (by decide) (choices 1) [1,2,16] r35513 c35513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20655
  · exact u20656
  · exact u20657

def r35514 : Route 9 := (fun mask => (mask,id))

def c35514 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35514 : Upper (D 7) (R 7) [34,192,72,257,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,160] 13 (by decide) (choices 1) [1,2,4,16] r35514 c35514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20658
  · exact u20659
  · exact u20660
  · exact u20661

def r35515 : Route 9 := (fun mask => (mask,id))

def c35515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35515 : Upper (D 7) (R 7) [34,192,72,258,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,258,160] 13 (by decide) (choices 1) [1,4,16] r35515 c35515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20662
  · exact u20663
  · exact u20664

def r35516 : Route 9 := (fun mask => (mask,id))

def c35516 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35516 : Upper (D 7) (R 7) [34,192,72,260,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,260,160] 13 (by decide) (choices 1) [1,2,16] r35516 c35516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20665
  · exact u20666
  · exact u20667

def r35517 : Route 9 := (fun mask => (mask,id))

def c35517 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35517 : Upper (D 7) (R 7) [34,192,72,272,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,160] 13 (by decide) (choices 1) [1,2,4] r35517 c35517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20668
  · exact u20669
  · exact u20670

def b35518 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 7 28 56 224 192 192 448), lower := (rows 35 259 7 28 56 32 64 128 256), losses := [] }

theorem u35518 : Upper (D 7) (R 7) [34,257,3,20,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35519 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 28 88 224 224 224 480), lower := (rows 35 259 7 28 88 32 64 128 256), losses := [] }

theorem u35519 : Upper (D 7) (R 7) [34,257,3,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u35519
end Delivery.IrregularNine14.P07
