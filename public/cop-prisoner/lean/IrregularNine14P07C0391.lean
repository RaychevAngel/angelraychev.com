import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0124
import IrregularNine14P07C0125

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23460 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 196 280 176 33 67 131 259), lower := (rows 37 74 196 280 176 33 64 128 256), losses := [] }

theorem u23460 : Upper (D 7) (R 7) [36,72,192,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23461 : Route 9 := (fun mask => (mask,id))

def c23461 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23461 : Upper (D 7) (R 7) [36,72,192,272,160,2] 13 := by
  apply FastRouting.sound _ _ [36,72,192,272,160,2] 13 (by decide) (choices 1) [1,2] r23461 c23461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7471
  · exact u7472

def b23462 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 196, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 74 196 296 19 33 210 146 402), lower := (rows 37 74 196 296 19 33 64 128 256), losses := [] }

theorem u23462 : Upper (D 7) (R 7) [36,72,192,288,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23463 : Route 9 := (fun mask => (mask,id))

def c23463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23463 : Upper (D 7) (R 7) [36,72,192,288,3,2] 13 := by
  apply FastRouting.sound _ _ [36,72,192,288,3,2] 13 (by decide) (choices 1) [1,16,128] r23463 c23463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7473
  · exact u7474
  · exact u7475

def r23464 : Route 9 := (fun mask => (mask,id))

def c23464 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23464 : Upper (D 7) (R 7) [36,72,192,288,3,16] 13 := by
  apply FastRouting.sound _ _ [36,72,192,288,3,16] 13 (by decide) (choices 1) [1,2,128] r23464 c23464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7476
  · exact u7477
  · exact u7478

def b23465 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 74 196 296 19 160 83 147 275), lower := (rows 37 74 196 296 19 160 64 128 256), losses := [] }

theorem u23465 : Upper (D 7) (R 7) [36,72,192,288,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23466 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 196 296 145 33 82 146 274), lower := (rows 37 74 196 296 145 33 64 128 256), losses := [] }

theorem u23466 : Upper (D 7) (R 7) [36,72,192,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23467 : Route 9 := (fun mask => (mask,id))

def c23467 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23467 : Upper (D 7) (R 7) [36,72,192,288,129,2] 13 := by
  apply FastRouting.sound _ _ [36,72,192,288,129,2] 13 (by decide) (choices 1) [1,2,16] r23467 c23467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7479
  · exact u7480
  · exact u7481

def b23468 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 74 196 296 145 48 67 131 259), lower := (rows 37 74 196 296 145 48 64 128 256), losses := [] }

theorem u23468 : Upper (D 7) (R 7) [36,72,192,288,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23468 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23469 : Route 9 := (fun mask => (mask,id))

def c23469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23469 : Upper (D 7) (R 7) [36,72,192,288,130,1] 13 := by
  apply FastRouting.sound _ _ [36,72,192,288,130,1] 13 (by decide) (choices 1) [1,2,16] r23469 c23469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7482
  · exact u7483
  · exact u7484

def r23470 : Route 9 := (fun mask => (mask,id))

def c23470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23470 : Upper (D 7) (R 7) [36,72,192,288,130,2] 13 := by
  apply FastRouting.sound _ _ [36,72,192,288,130,2] 13 (by decide) (choices 1) [1,16] r23470 c23470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7485
  · exact u7486

def r23471 : Route 9 := (fun mask => (mask,id))

def c23471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23471 : Upper (D 7) (R 7) [36,72,192,288,130,16] 13 := by
  apply FastRouting.sound _ _ [36,72,192,288,130,16] 13 (by decide) (choices 1) [1,2] r23471 c23471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7487
  · exact u7488

def b23472 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(3,6)], upper := (rows 37 74 196 392 19 33 114 178 306), lower := (rows 37 74 196 392 19 33 64 128 256), losses := [] }

theorem u23472 : Upper (D 7) (R 7) [36,72,192,384,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23473 : Route 9 := (fun mask => (mask,id))

def c23473 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23473 : Upper (D 7) (R 7) [36,72,192,384,3,2] 13 := by
  apply FastRouting.sound _ _ [36,72,192,384,3,2] 13 (by decide) (choices 1) [1,16,32] r23473 c23473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7489
  · exact u7490
  · exact u7491

def r23474 : Route 9 := (fun mask => (mask,id))

def c23474 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23474 : Upper (D 7) (R 7) [36,72,192,384,3,16] 13 := by
  apply FastRouting.sound _ _ [36,72,192,384,3,16] 13 (by decide) (choices 1) [1,2,32] r23474 c23474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7492
  · exact u7493
  · exact u7494

def r23475 : Route 9 := (fun mask => (mask,id))

def c23475 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23475 : Upper (D 7) (R 7) [36,72,192,384,34,1] 13 := by
  apply FastRouting.sound _ _ [36,72,192,384,34,1] 13 (by decide) (choices 1) [1,2,16] r23475 c23475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7495
  · exact u7496
  · exact u7497

def b23476 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 74 196 392 50 34 81 145 273), lower := (rows 37 74 196 392 50 34 64 128 256), losses := [] }

theorem u23476 : Upper (D 7) (R 7) [36,72,192,384,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23477 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 196 392 50 48 67 131 259), lower := (rows 37 74 196 392 50 48 64 128 256), losses := [] }

theorem u23477 : Upper (D 7) (R 7) [36,72,192,384,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23477 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23478 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 26 145 34 448 448 448), lower := (rows 37 98 13 26 145 34 64 128 256), losses := [] }

theorem u23478 : Upper (D 7) (R 7) [36,96,9,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23479 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 26 145 96 450 386 386), lower := (rows 37 98 13 26 145 96 64 128 256), losses := [] }

theorem u23479 : Upper (D 7) (R 7) [36,96,9,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23480 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 37 98 13 26 145 160 322 450 322), lower := (rows 37 98 13 26 145 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 96 13 61 177 160 64 160 256) }] }

theorem u23480 : Upper (D 7) (R 7) [36,96,9,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23481 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 37 98 13 26 145 288 194 194 450), lower := (rows 37 98 13 26 145 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 20 0 74 138 266), good := (rows 21 450 477 474 145 256 64 128 256) }] }

theorem u23481 : Upper (D 7) (R 7) [36,96,9,18,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23481 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23482 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 13 26 208 33 450 386 386), lower := (rows 37 98 13 26 208 33 64 128 256), losses := [] }

theorem u23482 : Upper (D 7) (R 7) [36,96,9,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23483 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 98 13 26 208 34 449 385 385), lower := (rows 37 98 13 26 208 34 64 128 256), losses := [] }

theorem u23483 : Upper (D 7) (R 7) [36,96,9,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23484 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 42, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 98 13 26 208 160 323 387 259), lower := (rows 37 98 13 26 208 160 64 128 256), losses := [] }

theorem u23484 : Upper (D 7) (R 7) [36,96,9,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23485 : Route 9 := (fun mask => (mask,id))

def c23485 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23485 : Upper (D 7) (R 7) [36,96,9,18,192,256] 13 := by
  apply FastRouting.sound _ _ [36,96,9,18,192,256] 13 (by decide) (choices 1) [1,2,128] r23485 c23485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7498
  · exact u7499
  · exact u7500

def b23486 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 26 273 34 192 192 448), lower := (rows 37 98 13 26 273 34 64 128 256), losses := [] }

theorem u23486 : Upper (D 7) (R 7) [36,96,9,18,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23487 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 26 273 96 194 130 386), lower := (rows 37 98 13 26 273 96 64 128 256), losses := [] }

theorem u23487 : Upper (D 7) (R 7) [36,96,9,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23488 : Route 9 := (fun mask => (mask,id))

def c23488 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23488 : Upper (D 7) (R 7) [36,96,9,18,257,128] 13 := by
  apply FastRouting.sound _ _ [36,96,9,18,257,128] 13 (by decide) (choices 1) [2,128] r23488 c23488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7501
  · exact u7502

def b23489 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 13 26 336 33 194 130 386), lower := (rows 37 98 13 26 336 33 64 128 256), losses := [] }

theorem u23489 : Upper (D 7) (R 7) [36,96,9,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23490 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 98 13 26 336 34 193 129 385), lower := (rows 37 98 13 26 336 34 64 128 256), losses := [] }

theorem u23490 : Upper (D 7) (R 7) [36,96,9,18,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23491 : Route 9 := (fun mask => (mask,id))

def c23491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23491 : Upper (D 7) (R 7) [36,96,9,18,320,128] 13 := by
  apply FastRouting.sound _ _ [36,96,9,18,320,128] 13 (by decide) (choices 1) [1,2,128] r23491 c23491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7503
  · exact u7504
  · exact u7505

def b23492 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 26 400 33 194 194 450), lower := (rows 37 98 13 26 400 33 64 128 256), losses := [] }

theorem u23492 : Upper (D 7) (R 7) [36,96,9,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23493 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 26 400 34 193 193 449), lower := (rows 37 98 13 26 400 34 64 128 256), losses := [] }

theorem u23493 : Upper (D 7) (R 7) [36,96,9,18,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23494 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 26 400 96 195 131 387), lower := (rows 37 98 13 26 400 96 64 128 256), losses := [] }

theorem u23494 : Upper (D 7) (R 7) [36,96,9,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23495 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(2,1)], upper := (rows 37 98 13 26 400 160 67 195 323), lower := (rows 37 98 13 26 400 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 96 13 61 432 160 64 160 256) },{ target := 6, region := (rows 9 2 12 8 16 176 0 128 256), good := (rows 37 34 13 63 432 160 0 160 256) }] }

theorem u23495 : Upper (D 7) (R 7) [36,96,9,18,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23496 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 88 145 34 450 386 386), lower := (rows 37 98 13 88 145 34 64 128 256), losses := [] }

theorem u23496 : Upper (D 7) (R 7) [36,96,9,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23497 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 37 98 13 88 145 160 322 386 258), lower := (rows 37 98 13 88 145 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 96 13 125 177 160 64 160 256) }] }

theorem u23497 : Upper (D 7) (R 7) [36,96,9,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23498 : Route 9 := (fun mask => (mask,id))

def c23498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23498 : Upper (D 7) (R 7) [36,96,9,80,129,256] 13 := by
  apply FastRouting.sound _ _ [36,96,9,80,129,256] 13 (by decide) (choices 1) [2,128] r23498 c23498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7506
  · exact u7507

def b23499 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 13 88 146 33 450 386 386), lower := (rows 37 98 13 88 146 33 64 128 256), losses := [] }

theorem u23499 : Upper (D 7) (R 7) [36,96,9,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23500 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 88 146 34 449 385 385), lower := (rows 37 98 13 88 146 34 64 128 256), losses := [] }

theorem u23500 : Upper (D 7) (R 7) [36,96,9,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23501 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 322, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 37 98 13 88 146 160 323 387 259), lower := (rows 37 98 13 88 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 36 98 14 122 178 160 64 160 256) },{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 96 13 125 176 160 64 160 256) }] }

theorem u23501 : Upper (D 7) (R 7) [36,96,9,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23502 : Route 9 := (fun mask => (mask,id))

def c23502 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23502 : Upper (D 7) (R 7) [36,96,9,80,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,9,80,130,256] 13 (by decide) (choices 1) [1,2,128] r23502 c23502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7508
  · exact u7509
  · exact u7510

def b23503 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 88 273 34 194 130 386), lower := (rows 37 98 13 88 273 34 64 128 256), losses := [] }

theorem u23503 : Upper (D 7) (R 7) [36,96,9,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23504 : Route 9 := (fun mask => (mask,id))

def c23504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23504 : Upper (D 7) (R 7) [36,96,9,80,257,128] 13 := by
  apply FastRouting.sound _ _ [36,96,9,80,257,128] 13 (by decide) (choices 1) [2,128] r23504 c23504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7511
  · exact u7512

def b23505 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 13 88 274 33 194 130 386), lower := (rows 37 98 13 88 274 33 64 128 256), losses := [] }

theorem u23505 : Upper (D 7) (R 7) [36,96,9,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23506 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 88 274 34 193 129 385), lower := (rows 37 98 13 88 274 34 64 128 256), losses := [] }

theorem u23506 : Upper (D 7) (R 7) [36,96,9,80,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23507 : Route 9 := (fun mask => (mask,id))

def c23507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23507 : Upper (D 7) (R 7) [36,96,9,80,258,128] 13 := by
  apply FastRouting.sound _ _ [36,96,9,80,258,128] 13 (by decide) (choices 1) [1,2,128] r23507 c23507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7513
  · exact u7514
  · exact u7515

def b23508 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 13 88 400 33 194 130 386), lower := (rows 37 98 13 88 400 33 64 128 256), losses := [] }

theorem u23508 : Upper (D 7) (R 7) [36,96,9,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23509 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 88 400 34 195 131 387), lower := (rows 37 98 13 88 400 34 64 128 256), losses := [] }

theorem u23509 : Upper (D 7) (R 7) [36,96,9,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23510 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 37 98 13 88 400 160 67 131 259), lower := (rows 37 98 13 88 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 36 98 14 122 432 160 64 160 256) },{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 96 13 125 432 160 64 160 256) }] }

theorem u23510 : Upper (D 7) (R 7) [36,96,9,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23511 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 138 81 34 464 400 400), lower := (rows 37 98 13 138 81 34 64 128 256), losses := [] }

theorem u23511 : Upper (D 7) (R 7) [36,96,9,130,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23512 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 13 138 81 48 450 386 386), lower := (rows 37 98 13 138 81 48 64 128 256), losses := [] }

theorem u23512 : Upper (D 7) (R 7) [36,96,9,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23512 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23513 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 138 81 160 338 402 274), lower := (rows 37 98 13 138 81 160 64 128 256), losses := [] }

theorem u23513 : Upper (D 7) (R 7) [36,96,9,130,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23514 : Route 9 := (fun mask => (mask,id))

def c23514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23514 : Upper (D 7) (R 7) [36,96,9,130,65,256] 13 := by
  apply FastRouting.sound _ _ [36,96,9,130,65,256] 13 (by decide) (choices 1) [2,16,128] r23514 c23514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7516
  · exact u7517
  · exact u7518

def b23515 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(2,6),(4,1),(4,6)], upper := (rows 37 98 13 138 145 34 336 464 336), lower := (rows 37 98 13 138 145 34 64 128 256), losses := [] }

theorem u23515 : Upper (D 7) (R 7) [36,96,9,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23516 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 13 138 145 48 322 450 322), lower := (rows 37 98 13 138 145 48 64 128 256), losses := [] }

theorem u23516 : Upper (D 7) (R 7) [36,96,9,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23516 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23517 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 138 145 96 338 402 274), lower := (rows 37 98 13 138 145 96 64 128 256), losses := [] }

theorem u23517 : Upper (D 7) (R 7) [36,96,9,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23518 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 13 138 145 288 82 210 338), lower := (rows 37 98 13 138 145 288 64 128 256), losses := [] }

theorem u23518 : Upper (D 7) (R 7) [36,96,9,130,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23518 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23519 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 138 208 33 338 402 274), lower := (rows 37 98 13 138 208 33 64 128 256), losses := [] }

theorem u23519 : Upper (D 7) (R 7) [36,96,9,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u23519
end Delivery.IrregularNine14.P07
