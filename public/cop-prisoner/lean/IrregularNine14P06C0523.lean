import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0224
import IrregularNine14P06C0225
import IrregularNine14P06C0226

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r31380 : Route 9 := (fun mask => (mask,id))

def c31380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31380 : Upper (D 6) (R 6) [10,36,129,96,260] 13 := by
  apply FastRouting.sound _ _ [10,36,129,96,260] 13 (by decide) (choices 1) [1,2,16,64] r31380 c31380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13462
  · exact u13463
  · exact u13464
  · exact u13465

def r31381 : Route 9 := (fun mask => (mask,id))

def c31381 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31381 : Upper (D 6) (R 6) [10,36,129,96,320] 13 := by
  apply FastRouting.sound _ _ [10,36,129,96,320] 13 (by decide) (choices 1) [1,2,4,16] r31381 c31381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13466
  · exact u13467
  · exact u13468
  · exact u13469

def b31382 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 16, targets := 96 },{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 11 38 133 265 22 112 112 240 368), lower := (rows 11 38 133 265 22 32 64 128 256), losses := [] }

theorem u31382 : Upper (D 6) (R 6) [10,36,129,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31383 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 38 133 265 50 116 84 212 340), lower := (rows 11 38 133 265 50 32 64 128 256), losses := [] }

theorem u31383 : Upper (D 6) (R 6) [10,36,129,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31384 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 133 265 52 114 82 210 338), lower := (rows 11 38 133 265 52 32 64 128 256), losses := [] }

theorem u31384 : Upper (D 6) (R 6) [10,36,129,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31385 : Route 9 := (fun mask => (mask,id))

def c31385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31385 : Upper (D 6) (R 6) [10,36,129,257,66] 13 := by
  apply FastRouting.sound _ _ [10,36,129,257,66] 13 (by decide) (choices 1) [4,16,64] r31385 c31385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13470
  · exact u13471
  · exact u13472

def r31386 : Route 9 := (fun mask => (mask,id))

def c31386 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31386 : Upper (D 6) (R 6) [10,36,129,257,68] 13 := by
  apply FastRouting.sound _ _ [10,36,129,257,68] 13 (by decide) (choices 1) [2,16,64] r31386 c31386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13473
  · exact u13474
  · exact u13475

def r31387 : Route 9 := (fun mask => (mask,id))

def c31387 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31387 : Upper (D 6) (R 6) [10,36,129,257,96] 13 := by
  apply FastRouting.sound _ _ [10,36,129,257,96] 13 (by decide) (choices 1) [2,4,16,64] r31387 c31387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13476
  · exact u13477
  · exact u13478
  · exact u13479

def b31388 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 38 133 268 19 112 112 240 368), lower := (rows 11 38 133 268 19 32 64 128 256), losses := [] }

theorem u31388 : Upper (D 6) (R 6) [10,36,129,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31389 : Route 9 := (fun mask => (mask,id))

def c31389 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31389 : Upper (D 6) (R 6) [10,36,129,260,33] 13 := by
  apply FastRouting.sound _ _ [10,36,129,260,33] 13 (by decide) (choices 1) [2,16,64] r31389 c31389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13480
  · exact u13481
  · exact u13482

def b31390 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 133 268 50 113 81 209 337), lower := (rows 11 38 133 268 50 32 64 128 256), losses := [] }

theorem u31390 : Upper (D 6) (R 6) [10,36,129,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31391 : Route 9 := (fun mask => (mask,id))

def c31391 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31391 : Upper (D 6) (R 6) [10,36,129,260,65] 13 := by
  apply FastRouting.sound _ _ [10,36,129,260,65] 13 (by decide) (choices 1) [2,16,64] r31391 c31391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13483
  · exact u13484
  · exact u13485

def r31392 : Route 9 := (fun mask => (mask,id))

def c31392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31392 : Upper (D 6) (R 6) [10,36,129,260,66] 13 := by
  apply FastRouting.sound _ _ [10,36,129,260,66] 13 (by decide) (choices 1) [1,16,64] r31392 c31392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13486
  · exact u13487
  · exact u13488

def r31393 : Route 9 := (fun mask => (mask,id))

def c31393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31393 : Upper (D 6) (R 6) [10,36,129,260,96] 13 := by
  apply FastRouting.sound _ _ [10,36,129,260,96] 13 (by decide) (choices 1) [1,2,16,64] r31393 c31393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13489
  · exact u13490
  · exact u13491
  · exact u13492

def b31394 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 133 280 19 100 100 228 356), lower := (rows 11 38 133 280 19 32 64 128 256), losses := [] }

theorem u31394 : Upper (D 6) (R 6) [10,36,129,272,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31395 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 38 133 280 21 98 98 226 354), lower := (rows 11 38 133 280 21 32 64 128 256), losses := [] }

theorem u31395 : Upper (D 6) (R 6) [10,36,129,272,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31396 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 133 280 22 97 97 225 353), lower := (rows 11 38 133 280 22 32 64 128 256), losses := [] }

theorem u31396 : Upper (D 6) (R 6) [10,36,129,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31397 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 11 38 133 280 49 102 70 198 326), lower := (rows 11 38 133 280 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 24 16 0 67 131 259), good := (rows 463 454 453 284 477 0 64 128 256) }] }

theorem u31397 : Upper (D 6) (R 6) [10,36,129,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31398 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 133 280 50 101 69 197 325), lower := (rows 11 38 133 280 50 32 64 128 256), losses := [] }

theorem u31398 : Upper (D 6) (R 6) [10,36,129,272,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31399 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 133 280 52 99 67 195 323), lower := (rows 11 38 133 280 52 32 64 128 256), losses := [] }

theorem u31399 : Upper (D 6) (R 6) [10,36,129,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31400 : Route 9 := (fun mask => (mask,id))

def c31400 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31400 : Upper (D 6) (R 6) [10,36,129,272,65] 13 := by
  apply FastRouting.sound _ _ [10,36,129,272,65] 13 (by decide) (choices 1) [2,4,64] r31400 c31400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13493
  · exact u13494
  · exact u13495

def r31401 : Route 9 := (fun mask => (mask,id))

def c31401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31401 : Upper (D 6) (R 6) [10,36,129,272,66] 13 := by
  apply FastRouting.sound _ _ [10,36,129,272,66] 13 (by decide) (choices 1) [1,4,64] r31401 c31401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13496
  · exact u13497
  · exact u13498

def r31402 : Route 9 := (fun mask => (mask,id))

def c31402 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31402 : Upper (D 6) (R 6) [10,36,129,272,68] 13 := by
  apply FastRouting.sound _ _ [10,36,129,272,68] 13 (by decide) (choices 1) [1,2,64] r31402 c31402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13499
  · exact u13500
  · exact u13501

def r31403 : Route 9 := (fun mask => (mask,id))

def c31403 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31403 : Upper (D 6) (R 6) [10,36,129,272,96] 13 := by
  apply FastRouting.sound _ _ [10,36,129,272,96] 13 (by decide) (choices 1) [1,2,4,64] r31403 c31403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13502
  · exact u13503
  · exact u13504
  · exact u13505

def b31404 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 38 133 296 19 116 84 212 340), lower := (rows 11 38 133 296 19 32 64 128 256), losses := [] }

theorem u31404 : Upper (D 6) (R 6) [10,36,129,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31405 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 38 133 296 21 114 82 210 338), lower := (rows 11 38 133 296 21 32 64 128 256), losses := [] }

theorem u31405 : Upper (D 6) (R 6) [10,36,129,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31406 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 133 296 22 113 81 209 337), lower := (rows 11 38 133 296 22 32 64 128 256), losses := [] }

theorem u31406 : Upper (D 6) (R 6) [10,36,129,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31407 : Route 9 := (fun mask => (mask,id))

def c31407 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31407 : Upper (D 6) (R 6) [10,36,129,288,65] 13 := by
  apply FastRouting.sound _ _ [10,36,129,288,65] 13 (by decide) (choices 1) [2,4,16,64] r31407 c31407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13506
  · exact u13507
  · exact u13508
  · exact u13509

def r31408 : Route 9 := (fun mask => (mask,id))

def c31408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31408 : Upper (D 6) (R 6) [10,36,129,288,66] 13 := by
  apply FastRouting.sound _ _ [10,36,129,288,66] 13 (by decide) (choices 1) [1,4,16,64] r31408 c31408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13510
  · exact u13511
  · exact u13512
  · exact u13513

def r31409 : Route 9 := (fun mask => (mask,id))

def c31409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31409 : Upper (D 6) (R 6) [10,36,129,288,68] 13 := by
  apply FastRouting.sound _ _ [10,36,129,288,68] 13 (by decide) (choices 1) [1,2,16,64] r31409 c31409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13514
  · exact u13515
  · exact u13516
  · exact u13517

def b31410 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 133 328 19 116 116 244 372), lower := (rows 11 38 133 328 19 32 64 128 256), losses := [] }

theorem u31410 : Upper (D 6) (R 6) [10,36,129,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31411 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 38 133 328 21 114 114 242 370), lower := (rows 11 38 133 328 21 32 64 128 256), losses := [] }

theorem u31411 : Upper (D 6) (R 6) [10,36,129,320,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31412 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 133 328 22 113 113 241 369), lower := (rows 11 38 133 328 22 32 64 128 256), losses := [] }

theorem u31412 : Upper (D 6) (R 6) [10,36,129,320,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31413 : Route 9 := (fun mask => (mask,id))

def c31413 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31413 : Upper (D 6) (R 6) [10,36,129,320,33] 13 := by
  apply FastRouting.sound _ _ [10,36,129,320,33] 13 (by decide) (choices 1) [2,4,16,64] r31413 c31413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13518
  · exact u13519
  · exact u13520
  · exact u13521

def b31414 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 133 328 50 117 85 213 341), lower := (rows 11 38 133 328 50 32 64 128 256), losses := [] }

theorem u31414 : Upper (D 6) (R 6) [10,36,129,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31415 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 133 328 52 115 83 211 339), lower := (rows 11 38 133 328 52 32 64 128 256), losses := [] }

theorem u31415 : Upper (D 6) (R 6) [10,36,129,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31416 : Route 9 := (fun mask => (mask,id))

def c31416 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31416 : Upper (D 6) (R 6) [10,36,129,320,65] 13 := by
  apply FastRouting.sound _ _ [10,36,129,320,65] 13 (by decide) (choices 1) [2,4,16] r31416 c31416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13522
  · exact u13523
  · exact u13524

def r31417 : Route 9 := (fun mask => (mask,id))

def c31417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31417 : Upper (D 6) (R 6) [10,36,129,320,66] 13 := by
  apply FastRouting.sound _ _ [10,36,129,320,66] 13 (by decide) (choices 1) [1,4,16] r31417 c31417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13525
  · exact u13526
  · exact u13527

def r31418 : Route 9 := (fun mask => (mask,id))

def c31418 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31418 : Upper (D 6) (R 6) [10,36,129,320,68] 13 := by
  apply FastRouting.sound _ _ [10,36,129,320,68] 13 (by decide) (choices 1) [1,2,16] r31418 c31418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13528
  · exact u13529
  · exact u13530

def r31419 : Route 9 := (fun mask => (mask,id))

def c31419 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31419 : Upper (D 6) (R 6) [10,36,129,320,96] 13 := by
  apply FastRouting.sound _ _ [10,36,129,320,96] 13 (by decide) (choices 1) [1,2,4,16] r31419 c31419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13531
  · exact u13532
  · exact u13533
  · exact u13534

def b31420 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 134 25 21 352 352 480 352), lower := (rows 11 38 134 25 21 32 64 128 256), losses := [] }

theorem u31420 : Upper (D 6) (R 6) [10,36,130,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31421 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 134 25 49 356 324 452 324), lower := (rows 11 38 134 25 49 32 64 128 256), losses := [] }

theorem u31421 : Upper (D 6) (R 6) [10,36,130,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31422 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 134 25 52 353 321 449 321), lower := (rows 11 38 134 25 52 32 64 128 256), losses := [] }

theorem u31422 : Upper (D 6) (R 6) [10,36,130,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31423 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 38 134 25 81 356 356 484 356), lower := (rows 11 38 134 25 81 32 64 128 256), losses := [] }

theorem u31423 : Upper (D 6) (R 6) [10,36,130,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31424 : Route 9 := (fun mask => (mask,id))

def c31424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31424 : Upper (D 6) (R 6) [10,36,130,17,68] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,68] 13 (by decide) (choices 1) [1,64,256] r31424 c31424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13535
  · exact u13536
  · exact u13537

def r31425 : Route 9 := (fun mask => (mask,id))

def c31425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31425 : Upper (D 6) (R 6) [10,36,130,17,96] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,96] 13 (by decide) (choices 1) [1,4,64,256] r31425 c31425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13538
  · exact u13539
  · exact u13540
  · exact u13541

def b31426 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 38 134 25 273 100 100 228 356), lower := (rows 11 38 134 25 273 32 64 128 256), losses := [] }

theorem u31426 : Upper (D 6) (R 6) [10,36,130,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31427 : Route 9 := (fun mask => (mask,id))

def c31427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31427 : Upper (D 6) (R 6) [10,36,130,17,260] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,260] 13 (by decide) (choices 1) [1,64] r31427 c31427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13542
  · exact u13543

def r31428 : Route 9 := (fun mask => (mask,id))

def c31428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31428 : Upper (D 6) (R 6) [10,36,130,17,288] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,288] 13 (by decide) (choices 1) [1,4,64] r31428 c31428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13544
  · exact u13545
  · exact u13546

def r31429 : Route 9 := (fun mask => (mask,id))

def c31429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31429 : Upper (D 6) (R 6) [10,36,130,17,320] 13 := by
  apply FastRouting.sound _ _ [10,36,130,17,320] 13 (by decide) (choices 1) [1,4,64] r31429 c31429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13547
  · exact u13548
  · exact u13549

def b31430 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 134 28 49 353 321 449 321), lower := (rows 11 38 134 28 49 32 64 128 256), losses := [] }

theorem u31430 : Upper (D 6) (R 6) [10,36,130,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31431 : Route 9 := (fun mask => (mask,id))

def c31431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31431 : Upper (D 6) (R 6) [10,36,130,20,65] 13 := by
  apply FastRouting.sound _ _ [10,36,130,20,65] 13 (by decide) (choices 1) [1,64,256] r31431 c31431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13550
  · exact u13551
  · exact u13552

def b31432 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 38 134 28 112 353 321 449 321), lower := (rows 11 38 134 28 112 32 64 128 256), losses := [] }

theorem u31432 : Upper (D 6) (R 6) [10,36,130,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31433 : Route 9 := (fun mask => (mask,id))

def c31433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31433 : Upper (D 6) (R 6) [10,36,130,20,257] 13 := by
  apply FastRouting.sound _ _ [10,36,130,20,257] 13 (by decide) (choices 1) [1,64] r31433 c31433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13553
  · exact u13554

def b31434 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 38 134 28 304 97 65 193 321), lower := (rows 11 38 134 28 304 32 64 128 256), losses := [] }

theorem u31434 : Upper (D 6) (R 6) [10,36,130,20,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31435 : Route 9 := (fun mask => (mask,id))

def c31435 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31435 : Upper (D 6) (R 6) [10,36,130,20,320] 13 := by
  apply FastRouting.sound _ _ [10,36,130,20,320] 13 (by decide) (choices 1) [1,64] r31435 c31435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13555
  · exact u13556

def b31436 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 134 56 21 353 321 449 321), lower := (rows 11 38 134 56 21 32 64 128 256), losses := [] }

theorem u31436 : Upper (D 6) (R 6) [10,36,130,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31437 : Route 9 := (fun mask => (mask,id))

def c31437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31437 : Upper (D 6) (R 6) [10,36,130,48,65] 13 := by
  apply FastRouting.sound _ _ [10,36,130,48,65] 13 (by decide) (choices 1) [1,4,64,256] r31437 c31437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13557
  · exact u13558
  · exact u13559
  · exact u13560

def r31438 : Route 9 := (fun mask => (mask,id))

def c31438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31438 : Upper (D 6) (R 6) [10,36,130,48,68] 13 := by
  apply FastRouting.sound _ _ [10,36,130,48,68] 13 (by decide) (choices 1) [1,64,256] r31438 c31438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13561
  · exact u13562
  · exact u13563

def r31439 : Route 9 := (fun mask => (mask,id))

def c31439 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31439 : Upper (D 6) (R 6) [10,36,130,48,257] 13 := by
  apply FastRouting.sound _ _ [10,36,130,48,257] 13 (by decide) (choices 1) [1,4,64] r31439 c31439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13564
  · exact u13565
  · exact u13566

#print axioms u31439
end Delivery.IrregularNine14.P06
