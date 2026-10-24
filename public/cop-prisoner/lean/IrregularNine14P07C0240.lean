import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0040

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14400 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 98 261 138 176 40 81 209 337), lower := (rows 7 98 261 138 176 40 64 128 256), losses := [] }

theorem u14400 : Upper (D 7) (R 7) [6,96,257,130,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14400 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14401 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 261 138 176 48 73 201 329), lower := (rows 7 98 261 138 176 48 64 128 256), losses := [] }

theorem u14401 : Upper (D 7) (R 7) [6,96,257,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14401 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14402 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 261 138 176 96 89 153 281), lower := (rows 7 98 261 138 176 96 64 128 256), losses := [] }

theorem u14402 : Upper (D 7) (R 7) [6,96,257,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14403 : Route 9 := (fun mask => (mask,id))

def c14403 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14403 : Upper (D 7) (R 7) [6,96,257,160,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,257,160,192,1] 13 (by decide) (choices 1) [2,8,16] r14403 c14403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2421
  · exact u2422
  · exact u2423

theorem m14404_1 : Upper (D 7) (R 7) [6,96,257,160,192,2,1] 13 :=
  permutation_upper _ _ _ [6,96,257,160,192,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2421

def r14404 : Route 9 := (fun mask => (mask,id))

def c14404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14404 : Upper (D 7) (R 7) [6,96,257,160,192,2] 13 := by
  apply FastRouting.sound _ _ [6,96,257,160,192,2] 13 (by decide) (choices 1) [1,8,16] r14404 c14404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m14404_1
  · exact u2424
  · exact u2425

def b14405 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 261 168 208 40 83 147 275), lower := (rows 7 98 261 168 208 40 64 128 256), losses := [] }

theorem u14405 : Upper (D 7) (R 7) [6,96,257,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14405 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14406 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 261 168 208 48 75 139 267), lower := (rows 7 98 261 168 208 48 64 128 256), losses := [] }

theorem u14406 : Upper (D 7) (R 7) [6,96,257,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14406 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14407 : Route 9 := (fun mask => (mask,id))

def c14407 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14407 : Upper (D 7) (R 7) [6,96,264,17,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,264,17,130,1] 13 (by decide) (choices 1) [32,128] r14407 c14407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2426
  · exact u2427

def b14408 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 25 146 96 225 161 417), lower := (rows 7 98 268 25 146 96 64 128 256), losses := [] }

theorem u14408 : Upper (D 7) (R 7) [6,96,264,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14409_1 : Upper (D 7) (R 7) [6,96,264,17,130,128,1] 13 :=
  permutation_upper _ _ _ [6,96,264,17,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2427

theorem m14409_32 : Upper (D 7) (R 7) [6,96,264,17,130,128,32] 13 :=
  permutation_upper _ _ _ [6,96,264,17,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2428

def r14409 : Route 9 := (fun mask => (mask,id))

def c14409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14409 : Upper (D 7) (R 7) [6,96,264,17,130,128] 13 := by
  apply FastRouting.sound _ _ [6,96,264,17,130,128] 13 (by decide) (choices 1) [1,32] r14409 c14409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14409_1
  · exact m14409_32

def b14410 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 210, targets := 1 }], pairs := [(1,0),(2,0),(2,5),(4,0)], upper := (rows 7 98 268 25 176 33 194 194 450), lower := (rows 7 98 268 25 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 50 12 8 50 32 123 187 315), good := (rows 470 498 460 478 498 498 64 128 256) },{ target := 5, region := (rows 1 2 12 8 16 0 67 131 259), good := (rows 455 450 268 477 144 449 64 128 256) }] }

theorem u14410 : Upper (D 7) (R 7) [6,96,264,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14411 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 452, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 7 98 268 25 176 34 193 193 449), lower := (rows 7 98 268 25 176 34 64 128 256), losses := [] }

theorem u14411 : Upper (D 7) (R 7) [6,96,264,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14412 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 25 176 96 195 131 387), lower := (rows 7 98 268 25 176 96 64 128 256), losses := [] }

theorem u14412 : Upper (D 7) (R 7) [6,96,264,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14413 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 268 25 176 160 67 195 323), lower := (rows 7 98 268 25 176 160 64 128 256), losses := [] }

theorem u14413 : Upper (D 7) (R 7) [6,96,264,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14414 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 5, region := 194, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(4,1)], upper := (rows 7 98 268 26 145 33 224 224 480), lower := (rows 7 98 268 26 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 12 8 16 32 98 162 290), good := (rows 454 482 268 478 144 482 64 128 256) },{ target := 1, region := (rows 1 0 12 8 49 49 123 187 315), good := (rows 501 496 460 508 497 497 64 128 256) }] }

theorem u14414 : Upper (D 7) (R 7) [6,96,264,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14415 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 26 145 96 225 161 417), lower := (rows 7 98 268 26 145 96 64 128 256), losses := [] }

theorem u14415 : Upper (D 7) (R 7) [6,96,264,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14416_1 : Upper (D 7) (R 7) [6,96,264,18,129,128,1] 13 :=
  permutation_upper _ _ _ [6,96,264,18,129,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2429

theorem m14416_32 : Upper (D 7) (R 7) [6,96,264,18,129,128,32] 13 :=
  permutation_upper _ _ _ [6,96,264,18,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2430

def r14416 : Route 9 := (fun mask => (mask,id))

def c14416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14416 : Upper (D 7) (R 7) [6,96,264,18,129,128] 13 := by
  apply FastRouting.sound _ _ [6,96,264,18,129,128] 13 (by decide) (choices 1) [1,32] r14416 c14416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14416_1
  · exact m14416_32

def r14417 : Route 9 := (fun mask => (mask,id))

def c14417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14417 : Upper (D 7) (R 7) [6,96,264,18,160,1] 13 := by
  apply FastRouting.sound _ _ [6,96,264,18,160,1] 13 (by decide) (choices 1) [1,128] r14417 c14417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2431
  · exact u2432

def b14418 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 26 176 96 193 129 385), lower := (rows 7 98 268 26 176 96 64 128 256), losses := [] }

theorem u14418 : Upper (D 7) (R 7) [6,96,264,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14419 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 98 268 26 176 160 65 193 321), lower := (rows 7 98 268 26 176 160 64 128 256), losses := [] }

theorem u14419 : Upper (D 7) (R 7) [6,96,264,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14419 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14420 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 268 41 81 34 208 144 400), lower := (rows 7 98 268 41 81 34 64 128 256), losses := [] }

theorem u14420 : Upper (D 7) (R 7) [6,96,264,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14420 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14421 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 268 41 81 48 194 130 386), lower := (rows 7 98 268 41 81 48 64 128 256), losses := [] }

theorem u14421 : Upper (D 7) (R 7) [6,96,264,33,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14421 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14422 : Route 9 := (fun mask => (mask,id))

def c14422 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14422 : Upper (D 7) (R 7) [6,96,264,33,65,128] 13 := by
  apply FastRouting.sound _ _ [6,96,264,33,65,128] 13 (by decide) (choices 1) [2,16,128] r14422 c14422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2433
  · exact u2434
  · exact u2435

def b14423 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 268 41 145 34 208 208 464), lower := (rows 7 98 268 41 145 34 64 128 256), losses := [] }

theorem u14423 : Upper (D 7) (R 7) [6,96,264,33,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14423 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14424 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 268 41 145 48 194 194 450), lower := (rows 7 98 268 41 145 48 64 128 256), losses := [] }

theorem u14424 : Upper (D 7) (R 7) [6,96,264,33,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14424 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14425 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 41 145 96 210 146 402), lower := (rows 7 98 268 41 145 96 64 128 256), losses := [] }

theorem u14425 : Upper (D 7) (R 7) [6,96,264,33,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14426 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 40, targets := 66 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(4,5)], upper := (rows 7 98 268 41 145 160 82 210 338), lower := (rows 7 98 268 41 145 160 64 128 256), losses := [] }

theorem u14426 : Upper (D 7) (R 7) [6,96,264,33,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14427 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 268 41 146 33 208 208 464), lower := (rows 7 98 268 41 146 33 64 128 256), losses := [] }

theorem u14427 : Upper (D 7) (R 7) [6,96,264,33,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14428 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 452, targets := 34 },{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 7 98 268 41 146 48 193 193 449), lower := (rows 7 98 268 41 146 48 64 128 256), losses := [] }

theorem u14428 : Upper (D 7) (R 7) [6,96,264,33,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14428 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14429 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 41 146 96 209 145 401), lower := (rows 7 98 268 41 146 96 64 128 256), losses := [] }

theorem u14429 : Upper (D 7) (R 7) [6,96,264,33,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14430 : Route 9 := (fun mask => (mask,id))

def c14430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14430 : Upper (D 7) (R 7) [6,96,264,33,130,128] 13 := by
  apply FastRouting.sound _ _ [6,96,264,33,130,128] 13 (by decide) (choices 1) [1,16] r14430 c14430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2436
  · exact u2437

def b14431 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 268 41 208 33 210 146 402), lower := (rows 7 98 268 41 208 33 64 128 256), losses := [] }

theorem u14431 : Upper (D 7) (R 7) [6,96,264,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14431 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14432 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 268 41 208 34 209 145 401), lower := (rows 7 98 268 41 208 34 64 128 256), losses := [] }

theorem u14432 : Upper (D 7) (R 7) [6,96,264,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14433 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 268 41 208 48 195 131 387), lower := (rows 7 98 268 41 208 48 64 128 256), losses := [] }

theorem u14433 : Upper (D 7) (R 7) [6,96,264,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14433 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14434 : Route 9 := (fun mask => (mask,id))

def c14434 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14434 : Upper (D 7) (R 7) [6,96,264,33,192,128] 13 := by
  apply FastRouting.sound _ _ [6,96,264,33,192,128] 13 (by decide) (choices 1) [1,2,16] r14434 c14434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2438
  · exact u2439
  · exact u2440

def b14435 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 454, targets := 1 },{ cop := 4, region := 40, targets := 66 }], pairs := [(1,0),(2,0),(3,1),(3,6)], upper := (rows 7 98 268 56 81 33 194 130 386), lower := (rows 7 98 268 56 81 33 64 128 256), losses := [] }

theorem u14435 : Upper (D 7) (R 7) [6,96,264,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14436 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 268 56 81 34 193 129 385), lower := (rows 7 98 268 56 81 34 64 128 256), losses := [] }

theorem u14436 : Upper (D 7) (R 7) [6,96,264,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14436 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14437 : Route 9 := (fun mask => (mask,id))

def c14437 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14437 : Upper (D 7) (R 7) [6,96,264,48,65,128] 13 := by
  apply FastRouting.sound _ _ [6,96,264,48,65,128] 13 (by decide) (choices 1) [1,2,128] r14437 c14437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2441
  · exact u2442
  · exact u2443

def b14438 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 40, targets := 194 },{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 98 268 56 145 33 194 194 450), lower := (rows 7 98 268 56 145 33 64 128 256), losses := [] }

theorem u14438 : Upper (D 7) (R 7) [6,96,264,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14439 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 7 98 268 56 145 34 193 193 449), lower := (rows 7 98 268 56 145 34 64 128 256), losses := [] }

theorem u14439 : Upper (D 7) (R 7) [6,96,264,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14440 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 56 145 96 195 131 387), lower := (rows 7 98 268 56 145 96 64 128 256), losses := [] }

theorem u14440 : Upper (D 7) (R 7) [6,96,264,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14441 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 98 268 56 145 160 67 195 323), lower := (rows 7 98 268 56 145 160 64 128 256), losses := [] }

theorem u14441 : Upper (D 7) (R 7) [6,96,264,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14442 : Route 9 := (fun mask => (mask,id))

def c14442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14442 : Upper (D 7) (R 7) [6,96,264,48,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,264,48,130,1] 13 (by decide) (choices 1) [1,128] r14442 c14442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2444
  · exact u2445

def b14443 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 56 146 96 193 129 385), lower := (rows 7 98 268 56 146 96 64 128 256), losses := [] }

theorem u14443 : Upper (D 7) (R 7) [6,96,264,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14444 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 98 268 56 146 160 65 193 321), lower := (rows 7 98 268 56 146 160 64 128 256), losses := [] }

theorem u14444 : Upper (D 7) (R 7) [6,96,264,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14445 : Route 9 := (fun mask => (mask,id))

def c14445 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14445 : Upper (D 7) (R 7) [6,96,264,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,264,48,192,1] 13 (by decide) (choices 1) [1,2,128] r14445 c14445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2446
  · exact u2447
  · exact u2448

def b14446 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 268 56 208 34 193 129 385), lower := (rows 7 98 268 56 208 34 64 128 256), losses := [] }

theorem u14446 : Upper (D 7) (R 7) [6,96,264,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14447 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 98 268 56 208 160 67 131 259), lower := (rows 7 98 268 56 208 160 64 128 256), losses := [] }

theorem u14447 : Upper (D 7) (R 7) [6,96,264,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14448 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 98 268 137 49 34 208 208 464), lower := (rows 7 98 268 137 49 34 64 128 256), losses := [] }

theorem u14448 : Upper (D 7) (R 7) [6,96,264,129,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14449 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 }], pairs := [(4,1),(4,6),(4,7)], upper := (rows 7 98 268 137 49 48 194 194 450), lower := (rows 7 98 268 137 49 48 64 128 256), losses := [] }

theorem u14449 : Upper (D 7) (R 7) [6,96,264,129,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14449 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14450 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 137 49 96 210 146 402), lower := (rows 7 98 268 137 49 96 64 128 256), losses := [] }

theorem u14450 : Upper (D 7) (R 7) [6,96,264,129,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14451 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 4, region := 66, targets := 1 },{ cop := 4, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,1),(4,6)], upper := (rows 7 98 268 137 49 160 82 210 338), lower := (rows 7 98 268 137 49 160 64 128 256), losses := [] }

theorem u14451 : Upper (D 7) (R 7) [6,96,264,129,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14452 : Route 9 := (fun mask => (mask,id))

def c14452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14452 : Upper (D 7) (R 7) [6,96,264,129,130,1] 13 := by
  apply FastRouting.sound _ _ [6,96,264,129,130,1] 13 (by decide) (choices 1) [16,32] r14452 c14452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2449
  · exact u2450

theorem m14453_1 : Upper (D 7) (R 7) [6,96,264,129,130,16,1] 13 :=
  permutation_upper _ _ _ [6,96,264,129,130,1,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2449

def r14453 : Route 9 := (fun mask => (mask,id))

def c14453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14453 : Upper (D 7) (R 7) [6,96,264,129,130,16] 13 := by
  apply FastRouting.sound _ _ [6,96,264,129,130,16] 13 (by decide) (choices 1) [1,32] r14453 c14453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14453_1
  · exact u2451

def b14454 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 137 146 96 113 177 305), lower := (rows 7 98 268 137 146 96 64 128 256), losses := [] }

theorem u14454 : Upper (D 7) (R 7) [6,96,264,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14455 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 5, region := 210, targets := 1 }], pairs := [(1,0),(4,0),(4,1),(4,6)], upper := (rows 7 98 268 137 176 33 82 210 338), lower := (rows 7 98 268 137 176 33 64 128 256), losses := [] }

theorem u14455 : Upper (D 7) (R 7) [6,96,264,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14456 : PairBound 9 := { available := 81, camps := [{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,6)], upper := (rows 7 98 268 137 176 34 81 209 337), lower := (rows 7 98 268 137 176 34 64 128 256), losses := [{ target := 0, region := (rows 0 66 4 8 24 99 64 128 256), good := (rows 38 98 284 184 176 34 98 128 256) },{ target := 6, region := (rows 1 2 4 8 24 35 0 128 256), good := (rows 39 34 284 185 176 34 0 128 256) }] }

theorem u14456 : Upper (D 7) (R 7) [6,96,264,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14457 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 98 268 137 176 48 67 195 323), lower := (rows 7 98 268 137 176 48 64 128 256), losses := [] }

theorem u14457 : Upper (D 7) (R 7) [6,96,264,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14457 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14458 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 268 137 176 96 83 147 275), lower := (rows 7 98 268 137 176 96 64 128 256), losses := [] }

theorem u14458 : Upper (D 7) (R 7) [6,96,264,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14459 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 1 },{ cop := 0, region := 48, targets := 64 }], pairs := [(1,0),(2,0),(3,0),(4,6)], upper := (rows 7 98 268 138 49 33 208 208 464), lower := (rows 7 98 268 138 49 33 64 128 256), losses := [] }

theorem u14459 : Upper (D 7) (R 7) [6,96,264,130,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u14459
end Delivery.IrregularNine14.P07
