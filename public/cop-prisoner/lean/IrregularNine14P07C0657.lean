import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0457
import IrregularNine14P07C0458

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39420 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 28 41 146 227 195 195 451), lower := (rows 37 322 28 41 146 32 64 128 256), losses := [] }

theorem u39420 : Upper (D 7) (R 7) [36,320,24,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39421 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 28 41 208 163 195 131 387), lower := (rows 37 322 28 41 208 32 64 128 256), losses := [] }

theorem u39421 : Upper (D 7) (R 7) [36,320,24,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39422 : Route 9 := (fun mask => (mask,id))

def c39422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39422 : Upper (D 7) (R 7) [36,320,24,34,65] 13 := by
  apply FastRouting.sound _ _ [36,320,24,34,65] 13 (by decide) (choices 1) [1,2,128] r39422 c39422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27423
  · exact u27424
  · exact u27425

def b39423 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 28 42 82 161 193 129 385), lower := (rows 37 322 28 42 82 32 64 128 256), losses := [] }

theorem u39423 : Upper (D 7) (R 7) [36,320,24,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39424 : Route 9 := (fun mask => (mask,id))

def c39424 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39424 : Upper (D 7) (R 7) [36,320,24,34,129] 13 := by
  apply FastRouting.sound _ _ [36,320,24,34,129] 13 (by decide) (choices 1) [1,2,64,128] r39424 c39424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27426
  · exact u27427
  · exact u27428
  · exact u27429

def r39425 : Route 9 := (fun mask => (mask,id))

def c39425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39425 : Upper (D 7) (R 7) [36,320,24,34,130] 13 := by
  apply FastRouting.sound _ _ [36,320,24,34,130] 13 (by decide) (choices 1) [1,64,128] r39425 c39425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27430
  · exact u27431
  · exact u27432

def r39426 : Route 9 := (fun mask => (mask,id))

def c39426 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39426 : Upper (D 7) (R 7) [36,320,24,34,192] 13 := by
  apply FastRouting.sound _ _ [36,320,24,34,192] 13 (by decide) (choices 1) [1,2,128] r39426 c39426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27433
  · exact u27434
  · exact u27435

def r39427 : Route 9 := (fun mask => (mask,id))

def c39427 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39427 : Upper (D 7) (R 7) [36,320,24,65,129] 13 := by
  apply FastRouting.sound _ _ [36,320,24,65,129] 13 (by decide) (choices 1) [2,128] r39427 c39427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27436
  · exact u27437

def r39428 : Route 9 := (fun mask => (mask,id))

def c39428 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39428 : Upper (D 7) (R 7) [36,320,24,65,130] 13 := by
  apply FastRouting.sound _ _ [36,320,24,65,130] 13 (by decide) (choices 1) [1,2,128] r39428 c39428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27438
  · exact u27439
  · exact u27440

def r39429 : Route 9 := (fun mask => (mask,id))

def c39429 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39429 : Upper (D 7) (R 7) [36,320,24,65,160] 13 := by
  apply FastRouting.sound _ _ [36,320,24,65,160] 13 (by decide) (choices 1) [1,2,128] r39429 c39429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27441
  · exact u27442
  · exact u27443

def b39430 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 28 74 145 163 227 163 419), lower := (rows 37 322 28 74 145 32 64 128 256), losses := [] }

theorem u39430 : Upper (D 7) (R 7) [36,320,24,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39431 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 28 74 146 161 225 161 417), lower := (rows 37 322 28 74 146 32 64 128 256), losses := [] }

theorem u39431 : Upper (D 7) (R 7) [36,320,24,66,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39432 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 8, targets := 161 },{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(3,0),(3,5),(3,7)], upper := (rows 37 322 28 74 176 163 195 131 387), lower := (rows 37 322 28 74 176 32 64 128 256), losses := [] }

theorem u39432 : Upper (D 7) (R 7) [36,320,24,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39433 : Route 9 := (fun mask => (mask,id))

def c39433 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39433 : Upper (D 7) (R 7) [36,320,24,96,129] 13 := by
  apply FastRouting.sound _ _ [36,320,24,96,129] 13 (by decide) (choices 1) [1,2,128] r39433 c39433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27444
  · exact u27445
  · exact u27446

def r39434 : Route 9 := (fun mask => (mask,id))

def c39434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39434 : Upper (D 7) (R 7) [36,320,24,96,130] 13 := by
  apply FastRouting.sound _ _ [36,320,24,96,130] 13 (by decide) (choices 1) [1,2,128] r39434 c39434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27447
  · exact u27448
  · exact u27449

def b39435 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 20, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(4,1)], upper := (rows 37 322 28 137 145 98 98 226 354), lower := (rows 37 322 28 137 145 32 64 128 256), losses := [] }

theorem u39435 : Upper (D 7) (R 7) [36,320,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39436 : Route 9 := (fun mask => (mask,id))

def c39436 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39436 : Upper (D 7) (R 7) [36,320,24,129,130] 13 := by
  apply FastRouting.sound _ _ [36,320,24,129,130] 13 (by decide) (choices 1) [1,2,64] r39436 c39436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27450
  · exact u27451
  · exact u27452

def b39437 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 13, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 28 137 176 99 67 195 323), lower := (rows 37 322 28 137 176 32 64 128 256), losses := [] }

theorem u39437 : Upper (D 7) (R 7) [36,320,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39437 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39438 : Route 9 := (fun mask => (mask,id))

def c39438 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39438 : Upper (D 7) (R 7) [36,320,24,129,192] 13 := by
  apply FastRouting.sound _ _ [36,320,24,129,192] 13 (by decide) (choices 1) [1,2] r39438 c39438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27453
  · exact u27454

def b39439 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 20, targets := 97 }], pairs := [(2,0),(2,5),(2,6),(4,0)], upper := (rows 37 322 28 138 146 97 97 225 353), lower := (rows 37 322 28 138 146 32 64 128 256), losses := [] }

theorem u39439 : Upper (D 7) (R 7) [36,320,24,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39440 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(3,5)], upper := (rows 37 322 28 138 176 99 67 195 323), lower := (rows 37 322 28 138 176 32 64 128 256), losses := [] }

theorem u39440 : Upper (D 7) (R 7) [36,320,24,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39441 : Route 9 := (fun mask => (mask,id))

def c39441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39441 : Upper (D 7) (R 7) [36,320,24,130,192] 13 := by
  apply FastRouting.sound _ _ [36,320,24,130,192] 13 (by decide) (choices 1) [1,2] r39441 c39441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27455
  · exact u27456

def b39442 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(4,5)], upper := (rows 37 322 28 168 208 35 67 131 259), lower := (rows 37 322 28 168 208 32 64 128 256), losses := [] }

theorem u39442 : Upper (D 7) (R 7) [36,320,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39443 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 16, targets := 160 }], pairs := [(1,0),(4,0),(4,5),(4,7)], upper := (rows 37 322 69 11 26 176 240 176 432), lower := (rows 37 322 69 11 26 32 64 128 256), losses := [] }

theorem u39443 : Upper (D 7) (R 7) [36,320,65,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39444 : Route 9 := (fun mask => (mask,id))

def c39444 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39444 : Upper (D 7) (R 7) [36,320,65,3,34] 13 := by
  apply FastRouting.sound _ _ [36,320,65,3,34] 13 (by decide) (choices 1) [8,16,128] r39444 c39444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27457
  · exact u27458
  · exact u27459

def b39445 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 176, targets := 64 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,0),(1,5),(4,0),(4,6)], upper := (rows 37 322 69 11 56 178 210 146 402), lower := (rows 37 322 69 11 56 32 64 128 256), losses := [] }

theorem u39445 : Upper (D 7) (R 7) [36,320,65,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39446 : Route 9 := (fun mask => (mask,id))

def c39446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39446 : Upper (D 7) (R 7) [36,320,65,3,130] 13 := by
  apply FastRouting.sound _ _ [36,320,65,3,130] 13 (by decide) (choices 1) [8,16,128] r39446 c39446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27460
  · exact u27461
  · exact u27462

def r39447 : Route 9 := (fun mask => (mask,id))

def c39447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39447 : Upper (D 7) (R 7) [36,320,65,3,136] 13 := by
  apply FastRouting.sound _ _ [36,320,65,3,136] 13 (by decide) (choices 1) [2,16,128] r39447 c39447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27463
  · exact u27464
  · exact u27465

def r39448 : Route 9 := (fun mask => (mask,id))

def c39448 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39448 : Upper (D 7) (R 7) [36,320,65,3,160] 13 := by
  apply FastRouting.sound _ _ [36,320,65,3,160] 13 (by decide) (choices 1) [2,8,16,128] r39448 c39448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27466
  · exact u27467
  · exact u27468
  · exact u27469

def r39449 : Route 9 := (fun mask => (mask,id))

def c39449 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39449 : Upper (D 7) (R 7) [36,320,65,17,10] 13 := by
  apply FastRouting.sound _ _ [36,320,65,17,10] 13 (by decide) (choices 1) [2,128] r39449 c39449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27470
  · exact u27471

def b39450 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 322 69 25 50 170 202 138 394), lower := (rows 37 322 69 25 50 32 64 128 256), losses := [] }

theorem u39450 : Upper (D 7) (R 7) [36,320,65,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39451 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 322 69 25 56 162 194 130 386), lower := (rows 37 322 69 25 56 32 64 128 256), losses := [] }

theorem u39451 : Upper (D 7) (R 7) [36,320,65,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39452 : Route 9 := (fun mask => (mask,id))

def c39452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39452 : Upper (D 7) (R 7) [36,320,65,17,130] 13 := by
  apply FastRouting.sound _ _ [36,320,65,17,130] 13 (by decide) (choices 1) [2,8,128] r39452 c39452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27472
  · exact u27473
  · exact u27474

def r39453 : Route 9 := (fun mask => (mask,id))

def c39453 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39453 : Upper (D 7) (R 7) [36,320,65,17,136] 13 := by
  apply FastRouting.sound _ _ [36,320,65,17,136] 13 (by decide) (choices 1) [2,128] r39453 c39453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27475
  · exact u27476

def b39454 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 322 69 25 176 170 202 138 394), lower := (rows 37 322 69 25 176 32 64 128 256), losses := [] }

theorem u39454 : Upper (D 7) (R 7) [36,320,65,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39455 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 69 26 26 161 225 161 417), lower := (rows 37 322 69 26 26 32 64 128 256), losses := [] }

theorem u39455 : Upper (D 7) (R 7) [36,320,65,18,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39456 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 458, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 69 26 49 170 202 138 394), lower := (rows 37 322 69 26 49 32 64 128 256), losses := [] }

theorem u39456 : Upper (D 7) (R 7) [36,320,65,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39457 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 69 26 50 169 201 137 393), lower := (rows 37 322 69 26 50 32 64 128 256), losses := [] }

theorem u39457 : Upper (D 7) (R 7) [36,320,65,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39458 : Route 9 := (fun mask => (mask,id))

def c39458 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39458 : Upper (D 7) (R 7) [36,320,65,18,40] 13 := by
  apply FastRouting.sound _ _ [36,320,65,18,40] 13 (by decide) (choices 1) [1,2,128] r39458 c39458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27477
  · exact u27478
  · exact u27479

def r39459 : Route 9 := (fun mask => (mask,id))

def c39459 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39459 : Upper (D 7) (R 7) [36,320,65,18,129] 13 := by
  apply FastRouting.sound _ _ [36,320,65,18,129] 13 (by decide) (choices 1) [2,8,128] r39459 c39459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27480
  · exact u27481
  · exact u27482

def b39460 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 69 26 146 169 233 169 425), lower := (rows 37 322 69 26 146 32 64 128 256), losses := [] }

theorem u39460 : Upper (D 7) (R 7) [36,320,65,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39461 : Route 9 := (fun mask => (mask,id))

def c39461 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39461 : Upper (D 7) (R 7) [36,320,65,18,136] 13 := by
  apply FastRouting.sound _ _ [36,320,65,18,136] 13 (by decide) (choices 1) [1,2,128] r39461 c39461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27483
  · exact u27484
  · exact u27485

def r39462 : Route 9 := (fun mask => (mask,id))

def c39462 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39462 : Upper (D 7) (R 7) [36,320,65,18,160] 13 := by
  apply FastRouting.sound _ _ [36,320,65,18,160] 13 (by decide) (choices 1) [1,2,8,128] r39462 c39462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27486
  · exact u27487
  · exact u27488
  · exact u27489

def b39463 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 69 41 146 186 218 154 410), lower := (rows 37 322 69 41 146 32 64 128 256), losses := [] }

theorem u39463 : Upper (D 7) (R 7) [36,320,65,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39464 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 37 322 69 41 152 178 210 146 402), lower := (rows 37 322 69 41 152 32 64 128 256), losses := [] }

theorem u39464 : Upper (D 7) (R 7) [36,320,65,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39465 : Route 9 := (fun mask => (mask,id))

def c39465 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39465 : Upper (D 7) (R 7) [36,320,65,34,129] 13 := by
  apply FastRouting.sound _ _ [36,320,65,34,129] 13 (by decide) (choices 1) [2,8,16,128] r39465 c39465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27490
  · exact u27491
  · exact u27492
  · exact u27493

def r39466 : Route 9 := (fun mask => (mask,id))

def c39466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39466 : Upper (D 7) (R 7) [36,320,65,34,130] 13 := by
  apply FastRouting.sound _ _ [36,320,65,34,130] 13 (by decide) (choices 1) [1,8,16,128] r39466 c39466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27494
  · exact u27495
  · exact u27496
  · exact u27497

def r39467 : Route 9 := (fun mask => (mask,id))

def c39467 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39467 : Upper (D 7) (R 7) [36,320,65,34,136] 13 := by
  apply FastRouting.sound _ _ [36,320,65,34,136] 13 (by decide) (choices 1) [1,2,16,128] r39467 c39467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27498
  · exact u27499
  · exact u27500
  · exact u27501

def r39468 : Route 9 := (fun mask => (mask,id))

def c39468 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39468 : Upper (D 7) (R 7) [36,320,65,48,129] 13 := by
  apply FastRouting.sound _ _ [36,320,65,48,129] 13 (by decide) (choices 1) [2,8,128] r39468 c39468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27502
  · exact u27503
  · exact u27504

def r39469 : Route 9 := (fun mask => (mask,id))

def c39469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39469 : Upper (D 7) (R 7) [36,320,65,48,130] 13 := by
  apply FastRouting.sound _ _ [36,320,65,48,130] 13 (by decide) (choices 1) [1,2,8,128] r39469 c39469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27505
  · exact u27506
  · exact u27507
  · exact u27508

def r39470 : Route 9 := (fun mask => (mask,id))

def c39470 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39470 : Upper (D 7) (R 7) [36,320,65,48,136] 13 := by
  apply FastRouting.sound _ _ [36,320,65,48,136] 13 (by decide) (choices 1) [1,2,128] r39470 c39470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27509
  · exact u27510
  · exact u27511

def r39471 : Route 9 := (fun mask => (mask,id))

def c39471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39471 : Upper (D 7) (R 7) [36,320,65,129,130] 13 := by
  apply FastRouting.sound _ _ [36,320,65,129,130] 13 (by decide) (choices 1) [2,8,16] r39471 c39471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27512
  · exact u27513
  · exact u27514

def b39472 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7),(4,1),(4,5),(4,6)], upper := (rows 37 322 69 137 152 50 114 178 306), lower := (rows 37 322 69 137 152 32 64 128 256), losses := [] }

theorem u39472 : Upper (D 7) (R 7) [36,320,65,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39473 : Route 9 := (fun mask => (mask,id))

def c39473 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39473 : Upper (D 7) (R 7) [36,320,65,129,160] 13 := by
  apply FastRouting.sound _ _ [36,320,65,129,160] 13 (by decide) (choices 1) [2,8,16] r39473 c39473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27515
  · exact u27516
  · exact u27517

def b39474 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 322 69 138 146 57 121 185 313), lower := (rows 37 322 69 138 146 32 64 128 256), losses := [] }

theorem u39474 : Upper (D 7) (R 7) [36,320,65,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39475 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 99 }], pairs := [(4,0),(4,1),(4,5),(4,6)], upper := (rows 37 322 69 138 152 51 115 179 307), lower := (rows 37 322 69 138 152 32 64 128 256), losses := [] }

theorem u39475 : Upper (D 7) (R 7) [36,320,65,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39476 : Route 9 := (fun mask => (mask,id))

def c39476 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39476 : Upper (D 7) (R 7) [36,320,65,130,160] 13 := by
  apply FastRouting.sound _ _ [36,320,65,130,160] 13 (by decide) (choices 1) [1,2,8,16] r39476 c39476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27518
  · exact u27519
  · exact u27520
  · exact u27521

def b39477 : PairBound 9 := { available := 35, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 69 152 152 35 99 163 291), lower := (rows 37 322 69 152 152 32 64 128 256), losses := [] }

theorem u39477 : Upper (D 7) (R 7) [36,320,65,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39478 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 69 152 176 43 75 139 267), lower := (rows 37 322 69 152 176 32 64 128 256), losses := [] }

theorem u39478 : Upper (D 7) (R 7) [36,320,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39479 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 16, targets := 160 },{ cop := 4, region := 8, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 37 322 76 11 19 176 240 176 432), lower := (rows 37 322 76 11 19 32 64 128 256), losses := [] }

theorem u39479 : Upper (D 7) (R 7) [36,320,72,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u39479
end Delivery.IrregularNine14.P07
