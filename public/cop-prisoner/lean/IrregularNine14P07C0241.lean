import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0040
import IrregularNine14P07C0041

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14460 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 268 138 49 48 193 193 449), lower := (rows 7 98 268 138 49 48 64 128 256), losses := [] }

theorem u14460 : Upper (D 7) (R 7) [6,96,264,130,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14460 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14461 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 138 49 96 209 145 401), lower := (rows 7 98 268 138 49 96 64 128 256), losses := [] }

theorem u14461 : Upper (D 7) (R 7) [6,96,264,130,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14462 : Route 9 := (fun mask => (mask,id))

def c14462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14462 : Upper (D 7) (R 7) [6,96,264,130,33,128] 13 := by
  apply FastRouting.sound _ _ [6,96,264,130,33,128] 13 (by decide) (choices 1) [1,16] r14462 c14462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2452
  · exact u2453

def r14463 : Route 9 := (fun mask => (mask,id))

def c14463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14463 : Upper (D 7) (R 7) [6,96,264,130,129,1] 13 := by
  apply FastRouting.sound _ _ [6,96,264,130,129,1] 13 (by decide) (choices 1) [16,32] r14463 c14463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2454
  · exact u2455

theorem m14464_1 : Upper (D 7) (R 7) [6,96,264,130,129,16,1] 13 :=
  permutation_upper _ _ _ [6,96,264,130,129,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2454

def r14464 : Route 9 := (fun mask => (mask,id))

def c14464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14464 : Upper (D 7) (R 7) [6,96,264,130,129,16] 13 := by
  apply FastRouting.sound _ _ [6,96,264,130,129,16] 13 (by decide) (choices 1) [1,32] r14464 c14464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14464_1
  · exact u2456

def b14465 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 138 145 96 113 177 305), lower := (rows 7 98 268 138 145 96 64 128 256), losses := [] }

theorem u14465 : Upper (D 7) (R 7) [6,96,264,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14466 : Route 9 := (fun mask => (mask,id))

def c14466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14466 : Upper (D 7) (R 7) [6,96,264,130,160,1] 13 := by
  apply FastRouting.sound _ _ [6,96,264,130,160,1] 13 (by decide) (choices 1) [1,16] r14466 c14466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2457
  · exact u2458

def b14467 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 268 138 176 48 65 193 321), lower := (rows 7 98 268 138 176 48 64 128 256), losses := [] }

theorem u14467 : Upper (D 7) (R 7) [6,96,264,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14467 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14468 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 138 176 96 81 145 273), lower := (rows 7 98 268 138 176 96 64 128 256), losses := [] }

theorem u14468 : Upper (D 7) (R 7) [6,96,264,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14469 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 7 98 268 152 49 33 194 194 450), lower := (rows 7 98 268 152 49 33 64 128 256), losses := [] }

theorem u14469 : Upper (D 7) (R 7) [6,96,264,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14470 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 98 268 152 49 34 193 193 449), lower := (rows 7 98 268 152 49 34 64 128 256), losses := [] }

theorem u14470 : Upper (D 7) (R 7) [6,96,264,144,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14471 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 152 49 96 195 131 387), lower := (rows 7 98 268 152 49 96 64 128 256), losses := [] }

theorem u14471 : Upper (D 7) (R 7) [6,96,264,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14472 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 66, targets := 128 }], pairs := [(0,7),(1,7),(2,5),(3,5)], upper := (rows 7 98 268 152 49 160 67 195 323), lower := (rows 7 98 268 152 49 160 64 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 65 129 257), good := (rows 455 66 268 156 477 128 64 128 256) },{ target := 7, region := (rows 9 18 12 8 16 32 89 0 281), good := (rows 327 98 333 351 371 32 64 0 256) }] }

theorem u14472 : Upper (D 7) (R 7) [6,96,264,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14473 : Route 9 := (fun mask => (mask,id))

def c14473 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14473 : Upper (D 7) (R 7) [6,96,264,160,65,1] 13 := by
  apply FastRouting.sound _ _ [6,96,264,160,65,1] 13 (by decide) (choices 1) [2,16,128] r14473 c14473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2459
  · exact u2460
  · exact u2461

def b14474 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 7 98 268 168 81 34 209 145 401), lower := (rows 7 98 268 168 81 34 64 128 256), losses := [] }

theorem u14474 : Upper (D 7) (R 7) [6,96,264,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14475 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 268 168 81 48 195 131 387), lower := (rows 7 98 268 168 81 48 64 128 256), losses := [] }

theorem u14475 : Upper (D 7) (R 7) [6,96,264,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14475 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14476 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 98 268 168 81 160 83 147 275), lower := (rows 7 98 268 168 81 160 64 128 256), losses := [] }

theorem u14476 : Upper (D 7) (R 7) [6,96,264,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14477 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 40, targets := 66 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 98, targets := 128 }], pairs := [(1,7),(3,1),(3,6),(4,5)], upper := (rows 7 98 268 168 145 33 82 210 338), lower := (rows 7 98 268 168 145 33 64 128 256), losses := [] }

theorem u14477 : Upper (D 7) (R 7) [6,96,264,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14478 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 7 98 268 168 145 34 81 209 337), lower := (rows 7 98 268 168 145 34 64 128 256), losses := [] }

theorem u14478 : Upper (D 7) (R 7) [6,96,264,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14479 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 268 168 145 48 67 195 323), lower := (rows 7 98 268 168 145 48 64 128 256), losses := [] }

theorem u14479 : Upper (D 7) (R 7) [6,96,264,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14479 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14480 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 168 145 96 83 147 275), lower := (rows 7 98 268 168 145 96 64 128 256), losses := [] }

theorem u14480 : Upper (D 7) (R 7) [6,96,264,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14481 : Route 9 := (fun mask => (mask,id))

def c14481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14481 : Upper (D 7) (R 7) [6,96,264,160,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,264,160,130,1] 13 (by decide) (choices 1) [1,16] r14481 c14481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2462
  · exact u2463

def b14482 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 98 268 168 146 48 65 193 321), lower := (rows 7 98 268 168 146 48 64 128 256), losses := [] }

theorem u14482 : Upper (D 7) (R 7) [6,96,264,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14482 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14483 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 168 146 96 81 145 273), lower := (rows 7 98 268 168 146 96 64 128 256), losses := [] }

theorem u14483 : Upper (D 7) (R 7) [6,96,264,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14484 : Route 9 := (fun mask => (mask,id))

def c14484 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14484 : Upper (D 7) (R 7) [6,96,264,160,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,264,160,192,1] 13 (by decide) (choices 1) [1,2,16] r14484 c14484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2464
  · exact u2465
  · exact u2466

def b14485 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 42, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 7 98 268 168 208 34 81 145 273), lower := (rows 7 98 268 168 208 34 64 128 256), losses := [] }

theorem u14485 : Upper (D 7) (R 7) [6,96,264,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14486 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 268 168 208 48 67 131 259), lower := (rows 7 98 268 168 208 48 64 128 256), losses := [] }

theorem u14486 : Upper (D 7) (R 7) [6,96,264,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14486 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14487 : Route 9 := (fun mask => (mask,id))

def c14487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14487 : Upper (D 7) (R 7) [6,96,288,17,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,130,1] 13 (by decide) (choices 1) [8,128] r14487 c14487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2467
  · exact u2468

def b14488 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 484, targets := 2 }], pairs := [(2,1),(3,5),(4,5)], upper := (rows 7 98 292 25 146 40 193 193 449), lower := (rows 7 98 292 25 146 40 64 128 256), losses := [] }

theorem u14488 : Upper (D 7) (R 7) [6,96,288,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14488 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14489 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 292 25 146 96 201 137 393), lower := (rows 7 98 292 25 146 96 64 128 256), losses := [] }

theorem u14489 : Upper (D 7) (R 7) [6,96,288,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14490 : Route 9 := (fun mask => (mask,id))

def c14490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14490 : Upper (D 7) (R 7) [6,96,288,17,130,128] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,130,128] 13 (by decide) (choices 1) [1,8] r14490 c14490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2469
  · exact u2470

def b14491 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 5, region := 454, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(4,5)], upper := (rows 7 98 292 25 152 33 194 194 450), lower := (rows 7 98 292 25 152 33 64 128 256), losses := [] }

theorem u14491 : Upper (D 7) (R 7) [6,96,288,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14492 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 292 25 152 34 193 193 449), lower := (rows 7 98 292 25 152 34 64 128 256), losses := [] }

theorem u14492 : Upper (D 7) (R 7) [6,96,288,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14493 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 292 25 152 96 195 131 387), lower := (rows 7 98 292 25 152 96 64 128 256), losses := [] }

theorem u14493 : Upper (D 7) (R 7) [6,96,288,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14494 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 292 25 152 160 67 195 323), lower := (rows 7 98 292 25 152 160 64 128 256), losses := [] }

theorem u14494 : Upper (D 7) (R 7) [6,96,288,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14495 : Route 9 := (fun mask => (mask,id))

def c14495 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14495 : Upper (D 7) (R 7) [6,96,288,17,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,192,1] 13 (by decide) (choices 1) [2,8,128] r14495 c14495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2471
  · exact u2472
  · exact u2473

def b14496 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 292 25 208 34 201 137 393), lower := (rows 7 98 292 25 208 34 64 128 256), losses := [] }

theorem u14496 : Upper (D 7) (R 7) [6,96,288,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14497 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 292 25 208 40 195 131 387), lower := (rows 7 98 292 25 208 40 64 128 256), losses := [] }

theorem u14497 : Upper (D 7) (R 7) [6,96,288,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14497 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14498 : Route 9 := (fun mask => (mask,id))

def c14498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14498 : Upper (D 7) (R 7) [6,96,288,17,192,128] 13 := by
  apply FastRouting.sound _ _ [6,96,288,17,192,128] 13 (by decide) (choices 1) [1,2,8] r14498 c14498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2474
  · exact u2475
  · exact u2476

def r14499 : Route 9 := (fun mask => (mask,id))

def c14499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14499 : Upper (D 7) (R 7) [6,96,288,18,129,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,18,129,1] 13 (by decide) (choices 1) [8,128] r14499 c14499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2477
  · exact u2478

def b14500 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 98 292 26 145 40 193 193 449), lower := (rows 7 98 292 26 145 40 64 128 256), losses := [] }

theorem u14500 : Upper (D 7) (R 7) [6,96,288,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14500 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14501 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 292 26 145 96 201 137 393), lower := (rows 7 98 292 26 145 96 64 128 256), losses := [] }

theorem u14501 : Upper (D 7) (R 7) [6,96,288,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14502 : Route 9 := (fun mask => (mask,id))

def c14502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14502 : Upper (D 7) (R 7) [6,96,288,18,129,128] 13 := by
  apply FastRouting.sound _ _ [6,96,288,18,129,128] 13 (by decide) (choices 1) [1,8] r14502 c14502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2479
  · exact u2480

def r14503 : Route 9 := (fun mask => (mask,id))

def c14503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14503 : Upper (D 7) (R 7) [6,96,288,18,136,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,18,136,1] 13 (by decide) (choices 1) [1,128] r14503 c14503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2481
  · exact u2482

def b14504 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 292 26 152 96 193 129 385), lower := (rows 7 98 292 26 152 96 64 128 256), losses := [] }

theorem u14504 : Upper (D 7) (R 7) [6,96,288,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14505 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 292 26 152 160 65 193 321), lower := (rows 7 98 292 26 152 160 64 128 256), losses := [] }

theorem u14505 : Upper (D 7) (R 7) [6,96,288,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14506 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 292 73 145 34 216 152 408), lower := (rows 7 98 292 73 145 34 64 128 256), losses := [] }

theorem u14506 : Upper (D 7) (R 7) [6,96,288,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14507 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 292 73 145 40 210 146 402), lower := (rows 7 98 292 73 145 40 64 128 256), losses := [] }

theorem u14507 : Upper (D 7) (R 7) [6,96,288,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14507 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14508 : Route 9 := (fun mask => (mask,id))

def c14508 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14508 : Upper (D 7) (R 7) [6,96,288,65,129,16] 13 := by
  apply FastRouting.sound _ _ [6,96,288,65,129,16] 13 (by decide) (choices 1) [2,8,128] r14508 c14508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2483
  · exact u2484
  · exact u2485

def r14509 : Route 9 := (fun mask => (mask,id))

def c14509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14509 : Upper (D 7) (R 7) [6,96,288,65,129,128] 13 := by
  apply FastRouting.sound _ _ [6,96,288,65,129,128] 13 (by decide) (choices 1) [2,8,16] r14509 c14509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2486
  · exact u2487
  · exact u2488

def r14510 : Route 9 := (fun mask => (mask,id))

def c14510 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14510 : Upper (D 7) (R 7) [6,96,288,65,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,65,130,1] 13 (by decide) (choices 1) [8,16,128] r14510 c14510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2489
  · exact u2490
  · exact u2491

def b14511 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 7 98 292 73 146 40 209 145 401), lower := (rows 7 98 292 73 146 40 64 128 256), losses := [] }

theorem u14511 : Upper (D 7) (R 7) [6,96,288,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14511 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14512 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 98 292 73 146 48 201 137 393), lower := (rows 7 98 292 73 146 48 64 128 256), losses := [] }

theorem u14512 : Upper (D 7) (R 7) [6,96,288,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14512 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14513 : Route 9 := (fun mask => (mask,id))

def c14513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14513 : Upper (D 7) (R 7) [6,96,288,65,130,128] 13 := by
  apply FastRouting.sound _ _ [6,96,288,65,130,128] 13 (by decide) (choices 1) [1,8,16] r14513 c14513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2492
  · exact u2493
  · exact u2494

def r14514 : Route 9 := (fun mask => (mask,id))

def c14514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14514 : Upper (D 7) (R 7) [6,96,288,65,136,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,65,136,1] 13 (by decide) (choices 1) [2,16,128] r14514 c14514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2495
  · exact u2496
  · exact u2497

def b14515 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 292 73 152 34 209 145 401), lower := (rows 7 98 292 73 152 34 64 128 256), losses := [] }

theorem u14515 : Upper (D 7) (R 7) [6,96,288,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14516 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 7 98 292 73 152 48 195 131 387), lower := (rows 7 98 292 73 152 48 64 128 256), losses := [] }

theorem u14516 : Upper (D 7) (R 7) [6,96,288,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14516 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14517 : Route 9 := (fun mask => (mask,id))

def c14517 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14517 : Upper (D 7) (R 7) [6,96,288,65,136,128] 13 := by
  apply FastRouting.sound _ _ [6,96,288,65,136,128] 13 (by decide) (choices 1) [1,2,16] r14517 c14517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2498
  · exact u2499
  · exact u2500

def r14518 : Route 9 := (fun mask => (mask,id))

def c14518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14518 : Upper (D 7) (R 7) [6,96,288,80,129,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,80,129,1] 13 (by decide) (choices 1) [2,8,128] r14518 c14518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2501
  · exact u2502
  · exact u2503

def b14519 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 292 88 145 34 201 137 393), lower := (rows 7 98 292 88 145 34 64 128 256), losses := [] }

theorem u14519 : Upper (D 7) (R 7) [6,96,288,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14519
end Delivery.IrregularNine14.P07
