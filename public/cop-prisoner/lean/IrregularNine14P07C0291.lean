import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0071
import IrregularNine14P07C0072

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17460 : Route 9 := (fun mask => (mask,id))

def c17460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17460 : Upper (D 7) (R 7) [12,272,3,96,160,2] 13 := by
  apply FastRouting.sound _ _ [12,272,3,96,160,2] 13 (by decide) (choices 1) [1,128] r17460 c17460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4297
  · exact u4298

def b17461 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 274 7 104 176 96 195 131 387), lower := (rows 13 274 7 104 176 96 64 128 256), losses := [] }

theorem u17461 : Upper (D 7) (R 7) [12,272,3,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17462 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 274 7 104 176 160 67 195 323), lower := (rows 13 274 7 104 176 160 64 128 256), losses := [] }

theorem u17462 : Upper (D 7) (R 7) [12,272,3,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17463 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 274 37 73 50 34 192 192 448), lower := (rows 13 274 37 73 50 34 64 128 256), losses := [] }

theorem u17463 : Upper (D 7) (R 7) [12,272,33,65,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17464 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 37 73 50 96 194 130 386), lower := (rows 13 274 37 73 50 96 64 128 256), losses := [] }

theorem u17464 : Upper (D 7) (R 7) [12,272,33,65,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17464 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17465 : Route 9 := (fun mask => (mask,id))

def c17465 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17465 : Upper (D 7) (R 7) [12,272,33,65,34,128] 13 := by
  apply FastRouting.sound _ _ [12,272,33,65,34,128] 13 (by decide) (choices 1) [2,128] r17465 c17465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4299
  · exact u4300

def b17466 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 205, targets := 2 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 274 37 73 146 34 224 224 480), lower := (rows 13 274 37 73 146 34 64 128 256), losses := [] }

theorem u17466 : Upper (D 7) (R 7) [12,272,33,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17467 : PairBound 9 := { available := 162, camps := [{ cop := 5, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 37 73 146 96 226 162 418), lower := (rows 13 274 37 73 146 96 64 128 256), losses := [] }

theorem u17467 : Upper (D 7) (R 7) [12,272,33,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m17468_2 : Upper (D 7) (R 7) [12,272,33,65,130,128,2] 13 :=
  permutation_upper _ _ _ [12,272,33,65,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4301

theorem m17468_32 : Upper (D 7) (R 7) [12,272,33,65,130,128,32] 13 :=
  permutation_upper _ _ _ [12,272,33,65,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4302

def r17468 : Route 9 := (fun mask => (mask,id))

def c17468 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17468 : Upper (D 7) (R 7) [12,272,33,65,130,128] 13 := by
  apply FastRouting.sound _ _ [12,272,33,65,130,128] 13 (by decide) (choices 1) [2,32] r17468 c17468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m17468_2
  · exact m17468_32

def b17469 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 4, region := 322, targets := 32 }], pairs := [(0,5),(1,0),(1,5),(4,0)], upper := (rows 13 274 37 73 176 34 194 194 450), lower := (rows 13 274 37 73 176 34 64 128 256), losses := [{ target := 5, region := (rows 5 18 4 12 16 0 114 178 306), good := (rows 13 466 461 73 466 450 64 128 256) }] }

theorem u17469 : Upper (D 7) (R 7) [12,272,33,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17470 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 37 73 176 96 194 130 386), lower := (rows 13 274 37 73 176 96 64 128 256), losses := [] }

theorem u17470 : Upper (D 7) (R 7) [12,272,33,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17471 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 274 37 73 176 160 66 194 322), lower := (rows 13 274 37 73 176 160 64 128 256), losses := [] }

theorem u17471 : Upper (D 7) (R 7) [12,272,33,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17472 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 274 37 74 50 33 192 192 448), lower := (rows 13 274 37 74 50 33 64 128 256), losses := [] }

theorem u17472 : Upper (D 7) (R 7) [12,272,33,66,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17473 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 2, region := 402, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(4,7)], upper := (rows 13 274 37 74 50 96 193 129 385), lower := (rows 13 274 37 74 50 96 64 128 256), losses := [] }

theorem u17473 : Upper (D 7) (R 7) [12,272,33,66,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17474 : Route 9 := (fun mask => (mask,id))

def c17474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17474 : Upper (D 7) (R 7) [12,272,33,66,34,128] 13 := by
  apply FastRouting.sound _ _ [12,272,33,66,34,128] 13 (by decide) (choices 1) [1,128] r17474 c17474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4303
  · exact u4304

def b17475 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 37 74 112 33 194 130 386), lower := (rows 13 274 37 74 112 33 64 128 256), losses := [] }

theorem u17475 : Upper (D 7) (R 7) [12,272,33,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17476 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(4,7)], upper := (rows 13 274 37 74 112 34 193 129 385), lower := (rows 13 274 37 74 112 34 64 128 256), losses := [] }

theorem u17476 : Upper (D 7) (R 7) [12,272,33,66,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17477 : Route 9 := (fun mask => (mask,id))

def c17477 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17477 : Upper (D 7) (R 7) [12,272,33,66,96,128] 13 := by
  apply FastRouting.sound _ _ [12,272,33,66,96,128] 13 (by decide) (choices 1) [1,2,128] r17477 c17477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4305
  · exact u4306
  · exact u4307

def b17478 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 274 37 74 145 34 224 224 480), lower := (rows 13 274 37 74 145 34 64 128 256), losses := [] }

theorem u17478 : Upper (D 7) (R 7) [12,272,33,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17479 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 37 74 145 96 226 162 418), lower := (rows 13 274 37 74 145 96 64 128 256), losses := [] }

theorem u17479 : Upper (D 7) (R 7) [12,272,33,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17480 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 36, targets := 66 }], pairs := [(1,0),(2,1),(2,6),(3,0)], upper := (rows 13 274 37 74 145 160 98 226 354), lower := (rows 13 274 37 74 145 160 64 128 256), losses := [] }

theorem u17480 : Upper (D 7) (R 7) [12,272,33,66,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17481 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 274 37 74 146 33 224 224 480), lower := (rows 13 274 37 74 146 33 64 128 256), losses := [] }

theorem u17481 : Upper (D 7) (R 7) [12,272,33,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17482 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 402, targets := 64 },{ cop := 3, region := 37, targets := 2 }], pairs := [(0,1),(1,6),(2,1),(4,6)], upper := (rows 13 274 37 74 146 96 225 161 417), lower := (rows 13 274 37 74 146 96 64 128 256), losses := [] }

theorem u17482 : Upper (D 7) (R 7) [12,272,33,66,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17483 : Route 9 := (fun mask => (mask,id))

def c17483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17483 : Upper (D 7) (R 7) [12,272,33,66,130,128] 13 := by
  apply FastRouting.sound _ _ [12,272,33,66,130,128] 13 (by decide) (choices 1) [1,32] r17483 c17483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4308
  · exact u4309

def b17484 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 274 37 74 176 33 194 194 450), lower := (rows 13 274 37 74 176 33 64 128 256), losses := [] }

theorem u17484 : Upper (D 7) (R 7) [12,272,33,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17485 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 274 37 74 176 34 193 193 449), lower := (rows 13 274 37 74 176 34 64 128 256), losses := [] }

theorem u17485 : Upper (D 7) (R 7) [12,272,33,66,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17486 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 37 74 176 96 195 131 387), lower := (rows 13 274 37 74 176 96 64 128 256), losses := [] }

theorem u17486 : Upper (D 7) (R 7) [12,272,33,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17487 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 274 37 74 176 160 67 195 323), lower := (rows 13 274 37 74 176 160 64 128 256), losses := [] }

theorem u17487 : Upper (D 7) (R 7) [12,272,33,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17488 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 37 74 208 33 226 162 418), lower := (rows 13 274 37 74 208 33 64 128 256), losses := [] }

theorem u17488 : Upper (D 7) (R 7) [12,272,33,66,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17489 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 274 37 74 208 34 225 161 417), lower := (rows 13 274 37 74 208 34 64 128 256), losses := [] }

theorem u17489 : Upper (D 7) (R 7) [12,272,33,66,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17490 : Route 9 := (fun mask => (mask,id))

def c17490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17490 : Upper (D 7) (R 7) [12,272,33,66,192,128] 13 := by
  apply FastRouting.sound _ _ [12,272,33,66,192,128] 13 (by decide) (choices 1) [1,2,32] r17490 c17490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4310
  · exact u4311
  · exact u4312

def b17491 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 205, targets := 2 },{ cop := 4, region := 482, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,1)], upper := (rows 13 274 37 200 19 34 224 224 480), lower := (rows 13 274 37 200 19 34 64 128 256), losses := [] }

theorem u17491 : Upper (D 7) (R 7) [12,272,33,192,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17492 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 37 200 19 96 226 162 418), lower := (rows 13 274 37 200 19 96 64 128 256), losses := [] }

theorem u17492 : Upper (D 7) (R 7) [12,272,33,192,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17493 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 274 37 200 50 33 194 194 450), lower := (rows 13 274 37 200 50 33 64 128 256), losses := [] }

theorem u17493 : Upper (D 7) (R 7) [12,272,33,192,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17494 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 50, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 274 37 200 50 34 193 193 449), lower := (rows 13 274 37 200 50 34 64 128 256), losses := [] }

theorem u17494 : Upper (D 7) (R 7) [12,272,33,192,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17495 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 37 200 50 96 195 131 387), lower := (rows 13 274 37 200 50 96 64 128 256), losses := [] }

theorem u17495 : Upper (D 7) (R 7) [12,272,33,192,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17496 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 274 37 200 82 33 226 162 418), lower := (rows 13 274 37 200 82 33 64 128 256), losses := [] }

theorem u17496 : Upper (D 7) (R 7) [12,272,33,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17497 : Route 9 := (fun mask => (mask,id))

def c17497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17497 : Upper (D 7) (R 7) [12,272,33,192,66,2] 13 := by
  apply FastRouting.sound _ _ [12,272,33,192,66,2] 13 (by decide) (choices 1) [1,32,128] r17497 c17497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4313
  · exact u4314
  · exact u4315

def b17498 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 13 274 37 200 82 160 99 163 291), lower := (rows 13 274 37 200 82 160 64 128 256), losses := [] }

theorem u17498 : Upper (D 7) (R 7) [12,272,33,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17499 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 274 37 200 112 33 194 130 386), lower := (rows 13 274 37 200 112 33 64 128 256), losses := [] }

theorem u17499 : Upper (D 7) (R 7) [12,272,33,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17500 : Route 9 := (fun mask => (mask,id))

def c17500 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17500 : Upper (D 7) (R 7) [12,272,33,192,96,2] 13 := by
  apply FastRouting.sound _ _ [12,272,33,192,96,2] 13 (by decide) (choices 1) [1,2,128] r17500 c17500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4316
  · exact u4317
  · exact u4318

def b17501 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 53, targets := 2 },{ cop := 2, region := 338, targets := 128 }], pairs := [(0,1),(1,7),(2,1),(4,1)], upper := (rows 13 274 37 200 112 160 67 131 259), lower := (rows 13 274 37 200 112 160 64 128 256), losses := [] }

theorem u17501 : Upper (D 7) (R 7) [12,272,33,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17502 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 274 38 74 145 33 224 224 480), lower := (rows 13 274 38 74 145 33 64 128 256), losses := [] }

theorem u17502 : Upper (D 7) (R 7) [12,272,34,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17503 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 37, targets := 128 },{ cop := 0, region := 240, targets := 2 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(2,0),(2,7),(4,1)], upper := (rows 13 274 38 74 145 96 225 161 417), lower := (rows 13 274 38 74 145 96 64 128 256), losses := [] }

theorem u17503 : Upper (D 7) (R 7) [12,272,34,66,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17504 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 73, targets := 128 },{ cop := 0, region := 240, targets := 2 }], pairs := [(0,7),(2,0),(3,7),(4,1)], upper := (rows 13 274 38 74 145 160 97 225 353), lower := (rows 13 274 38 74 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 176 64 128 256), good := (rows 12 310 38 78 176 160 64 160 256) }] }

theorem u17504 : Upper (D 7) (R 7) [12,272,34,66,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17505 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 274 38 74 176 33 193 193 449), lower := (rows 13 274 38 74 176 33 64 128 256), losses := [] }

theorem u17505 : Upper (D 7) (R 7) [12,272,34,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17506 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,5),(0,7),(2,7),(3,5)], upper := (rows 13 274 38 74 176 96 193 129 385), lower := (rows 13 274 38 74 176 96 64 128 256), losses := [] }

theorem u17506 : Upper (D 7) (R 7) [12,272,34,66,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17507 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 274 38 74 176 160 65 193 321), lower := (rows 13 274 38 74 176 160 64 128 256), losses := [] }

theorem u17507 : Upper (D 7) (R 7) [12,272,34,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17508 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 200, targets := 1 },{ cop := 4, region := 322, targets := 1 }], pairs := [(1,0),(1,5),(3,0),(4,5)], upper := (rows 13 274 38 104 145 33 194 194 450), lower := (rows 13 274 38 104 145 33 64 128 256), losses := [] }

theorem u17508 : Upper (D 7) (R 7) [12,272,34,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17509 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 274 38 104 145 34 193 193 449), lower := (rows 13 274 38 104 145 34 64 128 256), losses := [] }

theorem u17509 : Upper (D 7) (R 7) [12,272,34,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17510 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 274 38 104 145 96 195 131 387), lower := (rows 13 274 38 104 145 96 64 128 256), losses := [] }

theorem u17510 : Upper (D 7) (R 7) [12,272,34,96,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17511 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 73, targets := 128 }], pairs := [(0,7),(1,5),(3,7),(4,5)], upper := (rows 13 274 38 104 145 160 67 195 323), lower := (rows 13 274 38 104 145 160 64 128 256), losses := [] }

theorem u17511 : Upper (D 7) (R 7) [12,272,34,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17512 : Route 9 := (fun mask => (mask,id))

def c17512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17512 : Upper (D 7) (R 7) [12,272,34,96,192,1] 13 := by
  apply FastRouting.sound _ _ [12,272,34,96,192,1] 13 (by decide) (choices 1) [1,2,128] r17512 c17512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4319
  · exact u4320
  · exact u4321

def b17513 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 274 38 104 208 34 193 129 385), lower := (rows 13 274 38 104 208 34 64 128 256), losses := [] }

theorem u17513 : Upper (D 7) (R 7) [12,272,34,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17514 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 2, region := 73, targets := 128 }], pairs := [(0,7),(1,5),(3,7),(4,5)], upper := (rows 13 274 38 104 208 160 67 131 259), lower := (rows 13 274 38 104 208 160 64 128 256), losses := [] }

theorem u17514 : Upper (D 7) (R 7) [12,272,34,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17515 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 201, targets := 2 },{ cop := 4, region := 36, targets := 192 }], pairs := [(0,1),(2,6),(2,7),(3,1)], upper := (rows 13 274 38 200 19 33 224 224 480), lower := (rows 13 274 38 200 19 33 64 128 256), losses := [] }

theorem u17515 : Upper (D 7) (R 7) [12,272,34,192,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17516 : Route 9 := (fun mask => (mask,id))

def c17516 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17516 : Upper (D 7) (R 7) [12,272,34,192,3,64] 13 := by
  apply FastRouting.sound _ _ [12,272,34,192,3,64] 13 (by decide) (choices 1) [1,32,128] r17516 c17516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4322
  · exact u4323
  · exact u4324

def b17517 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 450, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 13 274 38 200 49 33 194 194 450), lower := (rows 13 274 38 200 49 33 64 128 256), losses := [] }

theorem u17517 : Upper (D 7) (R 7) [12,272,34,192,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17518 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 274 38 200 49 34 193 193 449), lower := (rows 13 274 38 200 49 34 64 128 256), losses := [] }

theorem u17518 : Upper (D 7) (R 7) [12,272,34,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17519 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 4, region := 390, targets := 64 }], pairs := [(0,5),(1,6),(2,6),(3,5)], upper := (rows 13 274 38 200 49 96 195 131 387), lower := (rows 13 274 38 200 49 96 64 128 256), losses := [] }

theorem u17519 : Upper (D 7) (R 7) [12,272,34,192,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17519
end Delivery.IrregularNine14.P07
