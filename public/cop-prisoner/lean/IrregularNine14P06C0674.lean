import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0457
import IrregularNine14P06C0458

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40440 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 134 268 28 49 99 67 195 323), lower := (rows 97 134 268 28 49 32 64 128 256), losses := [] }

theorem u40440 : Upper (D 6) (R 6) [96,132,264,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40441 : Route 9 := (fun mask => (mask,id))

def c40441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40441 : Upper (D 6) (R 6) [96,132,264,20,34] 13 := by
  apply FastRouting.sound _ _ [96,132,264,20,34] 13 (by decide) (choices 1) [1,2,64] r40441 c40441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27440
  · exact u27441
  · exact u27442

def b40442 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 134 268 28 112 35 67 131 259), lower := (rows 97 134 268 28 112 32 64 128 256), losses := [] }

theorem u40442 : Upper (D 6) (R 6) [96,132,264,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40443 : Route 9 := (fun mask => (mask,id))

def c40443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40443 : Upper (D 6) (R 6) [96,132,264,34,3] 13 := by
  apply FastRouting.sound _ _ [96,132,264,34,3] 13 (by decide) (choices 1) [1,4,16,64] r40443 c40443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27443
  · exact u27444
  · exact u27445
  · exact u27446

def r40444 : Route 9 := (fun mask => (mask,id))

def c40444 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40444 : Upper (D 6) (R 6) [96,132,264,34,5] 13 := by
  apply FastRouting.sound _ _ [96,132,264,34,5] 13 (by decide) (choices 1) [1,2,16,64] r40444 c40444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27447
  · exact u27448
  · exact u27449
  · exact u27450

def b40445 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 97 134 268 42 22 113 81 209 337), lower := (rows 97 134 268 42 22 32 64 128 256), losses := [] }

theorem u40445 : Upper (D 6) (R 6) [96,132,264,34,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40446 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 134 268 42 81 55 87 151 279), lower := (rows 97 134 268 42 81 32 64 128 256), losses := [] }

theorem u40446 : Upper (D 6) (R 6) [96,132,264,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40447 : Route 9 := (fun mask => (mask,id))

def c40447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40447 : Upper (D 6) (R 6) [96,132,264,34,66] 13 := by
  apply FastRouting.sound _ _ [96,132,264,34,66] 13 (by decide) (choices 1) [1,4,16] r40447 c40447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27451
  · exact u27452
  · exact u27453

def r40448 : Route 9 := (fun mask => (mask,id))

def c40448 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40448 : Upper (D 6) (R 6) [96,132,264,34,68] 13 := by
  apply FastRouting.sound _ _ [96,132,264,34,68] 13 (by decide) (choices 1) [1,2,16] r40448 c40448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27454
  · exact u27455
  · exact u27456

def r40449 : Route 9 := (fun mask => (mask,id))

def c40449 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40449 : Upper (D 6) (R 6) [96,132,264,36,3] 13 := by
  apply FastRouting.sound _ _ [96,132,264,36,3] 13 (by decide) (choices 1) [1,2,16,64] r40449 c40449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27457
  · exact u27458
  · exact u27459
  · exact u27460

def b40450 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 134 268 44 81 51 83 147 275), lower := (rows 97 134 268 44 81 32 64 128 256), losses := [] }

theorem u40450 : Upper (D 6) (R 6) [96,132,264,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40451 : Route 9 := (fun mask => (mask,id))

def c40451 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40451 : Upper (D 6) (R 6) [96,132,264,36,66] 13 := by
  apply FastRouting.sound _ _ [96,132,264,36,66] 13 (by decide) (choices 1) [1,2,16] r40451 c40451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27461
  · exact u27462
  · exact u27463

def r40452 : Route 9 := (fun mask => (mask,id))

def c40452 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40452 : Upper (D 6) (R 6) [96,132,264,48,3] 13 := by
  apply FastRouting.sound _ _ [96,132,264,48,3] 13 (by decide) (choices 1) [1,2,4,64] r40452 c40452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27464
  · exact u27465
  · exact u27466
  · exact u27467

def b40453 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 4 },{ cop := 4, region := 194, targets := 32 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 97 134 268 56 21 99 67 195 323), lower := (rows 97 134 268 56 21 32 64 128 256), losses := [{ target := 5, region := (rows 1 26 12 8 16 0 80 144 272), good := (rows 65 134 270 478 471 0 64 128 256) }] }

theorem u40453 : Upper (D 6) (R 6) [96,132,264,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40454 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 97 134 268 56 22 99 67 195 323), lower := (rows 97 134 268 56 22 32 64 128 256), losses := [] }

theorem u40454 : Upper (D 6) (R 6) [96,132,264,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40455 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 97 134 268 56 81 39 71 135 263), lower := (rows 97 134 268 56 81 32 64 128 256), losses := [] }

theorem u40455 : Upper (D 6) (R 6) [96,132,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40456 : Route 9 := (fun mask => (mask,id))

def c40456 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40456 : Upper (D 6) (R 6) [96,132,264,48,66] 13 := by
  apply FastRouting.sound _ _ [96,132,264,48,66] 13 (by decide) (choices 1) [1,2,4] r40456 c40456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27468
  · exact u27469
  · exact u27470

def r40457 : Route 9 := (fun mask => (mask,id))

def c40457 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40457 : Upper (D 6) (R 6) [96,132,264,48,68] 13 := by
  apply FastRouting.sound _ _ [96,132,264,48,68] 13 (by decide) (choices 1) [1,2] r40457 c40457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27471
  · exact u27472

def b40458 : PairBound 9 := { available := 92, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 97 134 292 11 19 124 92 220 348), lower := (rows 97 134 292 11 19 32 64 128 256), losses := [] }

theorem u40458 : Upper (D 6) (R 6) [96,132,288,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40459 : Route 9 := (fun mask => (mask,id))

def c40459 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40459 : Upper (D 6) (R 6) [96,132,288,3,5] 13 := by
  apply FastRouting.sound _ _ [96,132,288,3,5] 13 (by decide) (choices 1) [2,8,16,64] r40459 c40459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27473
  · exact u27474
  · exact u27475
  · exact u27476

def b40460 : PairBound 9 := { available := 89, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 97 134 292 11 22 121 89 217 345), lower := (rows 97 134 292 11 22 32 64 128 256), losses := [] }

theorem u40460 : Upper (D 6) (R 6) [96,132,288,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40461 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 134 292 11 25 118 86 214 342), lower := (rows 97 134 292 11 25 32 64 128 256), losses := [] }

theorem u40461 : Upper (D 6) (R 6) [96,132,288,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40462 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 97 134 292 11 26 117 85 213 341), lower := (rows 97 134 292 11 26 32 64 128 256), losses := [] }

theorem u40462 : Upper (D 6) (R 6) [96,132,288,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40463 : Route 9 := (fun mask => (mask,id))

def c40463 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40463 : Upper (D 6) (R 6) [96,132,288,3,12] 13 := by
  apply FastRouting.sound _ _ [96,132,288,3,12] 13 (by decide) (choices 1) [1,2,16,64] r40463 c40463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27477
  · exact u27478
  · exact u27479
  · exact u27480

def b40464 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 134 292 11 81 62 94 158 286), lower := (rows 97 134 292 11 81 32 64 128 256), losses := [] }

theorem u40464 : Upper (D 6) (R 6) [96,132,288,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40465 : Route 9 := (fun mask => (mask,id))

def c40465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40465 : Upper (D 6) (R 6) [96,132,288,3,66] 13 := by
  apply FastRouting.sound _ _ [96,132,288,3,66] 13 (by decide) (choices 1) [1,4,8,16] r40465 c40465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27481
  · exact u27482
  · exact u27483
  · exact u27484

def r40466 : Route 9 := (fun mask => (mask,id))

def c40466 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40466 : Upper (D 6) (R 6) [96,132,288,3,68] 13 := by
  apply FastRouting.sound _ _ [96,132,288,3,68] 13 (by decide) (choices 1) [1,2,8,16] r40466 c40466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27485
  · exact u27486
  · exact u27487
  · exact u27488

def r40467 : Route 9 := (fun mask => (mask,id))

def c40467 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40467 : Upper (D 6) (R 6) [96,132,288,3,72] 13 := by
  apply FastRouting.sound _ _ [96,132,288,3,72] 13 (by decide) (choices 1) [1,2,4,16] r40467 c40467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27489
  · exact u27490
  · exact u27491
  · exact u27492

def b40468 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 134 292 13 25 114 82 210 338), lower := (rows 97 134 292 13 25 32 64 128 256), losses := [] }

theorem u40468 : Upper (D 6) (R 6) [96,132,288,5,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40469 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 97 134 292 13 26 115 83 211 339), lower := (rows 97 134 292 13 26 32 64 128 256), losses := [] }

theorem u40469 : Upper (D 6) (R 6) [96,132,288,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40470 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 134 292 13 81 58 90 154 282), lower := (rows 97 134 292 13 81 32 64 128 256), losses := [] }

theorem u40470 : Upper (D 6) (R 6) [96,132,288,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40471 : Route 9 := (fun mask => (mask,id))

def c40471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40471 : Upper (D 6) (R 6) [96,132,288,5,66] 13 := by
  apply FastRouting.sound _ _ [96,132,288,5,66] 13 (by decide) (choices 1) [1,2,8,16] r40471 c40471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27493
  · exact u27494
  · exact u27495
  · exact u27496

def r40472 : Route 9 := (fun mask => (mask,id))

def c40472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40472 : Upper (D 6) (R 6) [96,132,288,5,72] 13 := by
  apply FastRouting.sound _ _ [96,132,288,5,72] 13 (by decide) (choices 1) [1,2,16] r40472 c40472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27497
  · exact u27498
  · exact u27499

def b40473 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 134 292 14 25 115 83 211 339), lower := (rows 97 134 292 14 25 32 64 128 256), losses := [] }

theorem u40473 : Upper (D 6) (R 6) [96,132,288,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40474 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 134 292 14 26 113 81 209 337), lower := (rows 97 134 292 14 26 32 64 128 256), losses := [] }

theorem u40474 : Upper (D 6) (R 6) [96,132,288,6,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40475 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 134 292 14 82 57 89 153 281), lower := (rows 97 134 292 14 82 32 64 128 256), losses := [] }

theorem u40475 : Upper (D 6) (R 6) [96,132,288,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40476 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 134 292 14 88 51 83 147 275), lower := (rows 97 134 292 14 88 32 64 128 256), losses := [] }

theorem u40476 : Upper (D 6) (R 6) [96,132,288,6,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40477 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 134 292 25 25 102 70 198 326), lower := (rows 97 134 292 25 25 32 64 128 256), losses := [] }

theorem u40477 : Upper (D 6) (R 6) [96,132,288,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40478 : Route 9 := (fun mask => (mask,id))

def c40478 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40478 : Upper (D 6) (R 6) [96,132,288,17,10] 13 := by
  apply FastRouting.sound _ _ [96,132,288,17,10] 13 (by decide) (choices 1) [1,2,4,64] r40478 c40478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27500
  · exact u27501
  · exact u27502
  · exact u27503

def r40479 : Route 9 := (fun mask => (mask,id))

def c40479 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40479 : Upper (D 6) (R 6) [96,132,288,17,12] 13 := by
  apply FastRouting.sound _ _ [96,132,288,17,12] 13 (by decide) (choices 1) [1,2,64] r40479 c40479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27504
  · exact u27505
  · exact u27506

def b40480 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 134 292 25 81 46 78 142 270), lower := (rows 97 134 292 25 81 32 64 128 256), losses := [] }

theorem u40480 : Upper (D 6) (R 6) [96,132,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40481 : Route 9 := (fun mask => (mask,id))

def c40481 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40481 : Upper (D 6) (R 6) [96,132,288,17,66] 13 := by
  apply FastRouting.sound _ _ [96,132,288,17,66] 13 (by decide) (choices 1) [1,2,4,8] r40481 c40481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27507
  · exact u27508
  · exact u27509
  · exact u27510

def r40482 : Route 9 := (fun mask => (mask,id))

def c40482 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40482 : Upper (D 6) (R 6) [96,132,288,17,68] 13 := by
  apply FastRouting.sound _ _ [96,132,288,17,68] 13 (by decide) (choices 1) [1,2,8] r40482 c40482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27511
  · exact u27512
  · exact u27513

def b40483 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 134 292 25 88 39 71 135 263), lower := (rows 97 134 292 25 88 32 64 128 256), losses := [] }

theorem u40483 : Upper (D 6) (R 6) [96,132,288,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40484 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 24, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 134 292 26 26 101 69 197 325), lower := (rows 97 134 292 26 26 32 64 128 256), losses := [] }

theorem u40484 : Upper (D 6) (R 6) [96,132,288,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40485 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 134 292 26 28 99 67 195 323), lower := (rows 97 134 292 26 28 32 64 128 256), losses := [] }

theorem u40485 : Upper (D 6) (R 6) [96,132,288,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40486 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 134 292 26 81 47 79 143 271), lower := (rows 97 134 292 26 81 32 64 128 256), losses := [] }

theorem u40486 : Upper (D 6) (R 6) [96,132,288,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40487 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 134 292 26 82 45 77 141 269), lower := (rows 97 134 292 26 82 32 64 128 256), losses := [] }

theorem u40487 : Upper (D 6) (R 6) [96,132,288,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40488 : Route 9 := (fun mask => (mask,id))

def c40488 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40488 : Upper (D 6) (R 6) [96,132,288,18,68] 13 := by
  apply FastRouting.sound _ _ [96,132,288,18,68] 13 (by decide) (choices 1) [1,2,8] r40488 c40488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27514
  · exact u27515
  · exact u27516

def r40489 : Route 9 := (fun mask => (mask,id))

def c40489 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40489 : Upper (D 6) (R 6) [96,132,288,18,72] 13 := by
  apply FastRouting.sound _ _ [96,132,288,18,72] 13 (by decide) (choices 1) [1,2,4] r40489 c40489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27517
  · exact u27518
  · exact u27519

def b40490 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 134 292 28 81 43 75 139 267), lower := (rows 97 134 292 28 81 32 64 128 256), losses := [] }

theorem u40490 : Upper (D 6) (R 6) [96,132,288,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40491 : Route 9 := (fun mask => (mask,id))

def c40491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40491 : Upper (D 6) (R 6) [96,132,288,20,66] 13 := by
  apply FastRouting.sound _ _ [96,132,288,20,66] 13 (by decide) (choices 1) [1,2,8] r40491 c40491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27520
  · exact u27521
  · exact u27522

def b40492 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,6),(2,6)], upper := (rows 97 134 292 28 88 35 67 131 259), lower := (rows 97 134 292 28 88 32 64 128 256), losses := [] }

theorem u40492 : Upper (D 6) (R 6) [96,132,288,20,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40493 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 97 138 276 11 19 100 100 228 356), lower := (rows 97 138 276 11 19 32 64 128 256), losses := [] }

theorem u40493 : Upper (D 6) (R 6) [96,136,272,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m40494_4 : Upper (D 6) (R 6) [96,136,272,3,5,4] 13 :=
  permutation_upper _ _ _ [96,136,272,3,5,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27523

def r40494 : Route 9 := (fun mask => (mask,id))

def c40494 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40494 : Upper (D 6) (R 6) [96,136,272,3,5] 13 := by
  apply FastRouting.sound _ _ [96,136,272,3,5] 13 (by decide) (choices 1) [2,4,64] r40494 c40494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27523
  · exact m40494_4
  · exact u27524

def r40495 : Route 9 := (fun mask => (mask,id))

def c40495 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40495 : Upper (D 6) (R 6) [96,136,272,3,6] 13 := by
  apply FastRouting.sound _ _ [96,136,272,3,6] 13 (by decide) (choices 1) [1,4,64] r40495 c40495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27525
  · exact u27526
  · exact u27527

def b40496 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 138 276 11 49 102 70 198 326), lower := (rows 97 138 276 11 49 32 64 128 256), losses := [] }

theorem u40496 : Upper (D 6) (R 6) [96,136,272,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40497 : Route 9 := (fun mask => (mask,id))

def c40497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40497 : Upper (D 6) (R 6) [96,136,272,3,34] 13 := by
  apply FastRouting.sound _ _ [96,136,272,3,34] 13 (by decide) (choices 1) [1,4,64] r40497 c40497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27528
  · exact u27529
  · exact u27530

def r40498 : Route 9 := (fun mask => (mask,id))

def c40498 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40498 : Upper (D 6) (R 6) [96,136,272,3,36] 13 := by
  apply FastRouting.sound _ _ [96,136,272,3,36] 13 (by decide) (choices 1) [1,2,4,64] r40498 c40498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27531
  · exact u27532
  · exact u27533
  · exact u27534

def b40499 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 138 276 11 112 39 71 135 263), lower := (rows 97 138 276 11 112 32 64 128 256), losses := [] }

theorem u40499 : Upper (D 6) (R 6) [96,136,272,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u40499
end Delivery.IrregularNine14.P06
