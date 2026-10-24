import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0107

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17460 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 38 200 112 177 209 145 401), lower := (rows 289 14 38 200 112 32 64 128 256), losses := [] }

theorem u17460 : Upper (D 8) (R 8) [288,12,34,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17461 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 14 38 200 208 49 113 177 305), lower := (rows 289 14 38 200 208 32 64 128 256), losses := [] }

theorem u17461 : Upper (D 8) (R 8) [288,12,34,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17462 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 52 73 49 226 194 194 450), lower := (rows 289 14 52 73 49 32 64 128 256), losses := [] }

theorem u17462 : Upper (D 8) (R 8) [288,12,48,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17463 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 14 52 73 50 225 193 193 449), lower := (rows 289 14 52 73 50 32 64 128 256), losses := [] }

theorem u17463 : Upper (D 8) (R 8) [288,12,48,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17464 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 52 73 81 162 226 162 418), lower := (rows 289 14 52 73 81 32 64 128 256), losses := [] }

theorem u17464 : Upper (D 8) (R 8) [288,12,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17465 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 73 82 161 225 161 417), lower := (rows 289 14 52 73 82 32 64 128 256), losses := [] }

theorem u17465 : Upper (D 8) (R 8) [288,12,48,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17466 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 14 52 73 112 163 195 131 387), lower := (rows 289 14 52 73 112 32 64 128 256), losses := [] }

theorem u17466 : Upper (D 8) (R 8) [288,12,48,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17467 : Route 9 := (fun mask => (mask,id))

def c17467 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17467 : Upper (D 8) (R 8) [288,12,48,65,129] 13 := by
  apply FastRouting.sound _ _ [288,12,48,65,129] 13 (by decide) (choices 1) [2,64,128] r17467 c17467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6451
  · exact u6452
  · exact u6453

def r17468 : Route 9 := (fun mask => (mask,id))

def c17468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17468 : Upper (D 8) (R 8) [288,12,48,65,130] 13 := by
  apply FastRouting.sound _ _ [288,12,48,65,130] 13 (by decide) (choices 1) [1,64,128] r17468 c17468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6454
  · exact u6455
  · exact u6456

def b17469 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 14 52 73 176 227 195 195 451), lower := (rows 289 14 52 73 176 32 64 128 256), losses := [] }

theorem u17469 : Upper (D 8) (R 8) [288,12,48,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17470 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 73 208 163 227 163 419), lower := (rows 289 14 52 73 208 32 64 128 256), losses := [] }

theorem u17470 : Upper (D 8) (R 8) [288,12,48,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17471 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 52 74 49 225 193 193 449), lower := (rows 289 14 52 74 49 32 64 128 256), losses := [] }

theorem u17471 : Upper (D 8) (R 8) [288,12,48,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17472 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 74 81 161 225 161 417), lower := (rows 289 14 52 74 81 32 64 128 256), losses := [] }

theorem u17472 : Upper (D 8) (R 8) [288,12,48,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17473 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 52 74 112 161 193 129 385), lower := (rows 289 14 52 74 112 32 64 128 256), losses := [] }

theorem u17473 : Upper (D 8) (R 8) [288,12,48,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17474 : Route 9 := (fun mask => (mask,id))

def c17474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17474 : Upper (D 8) (R 8) [288,12,48,66,129] 13 := by
  apply FastRouting.sound _ _ [288,12,48,66,129] 13 (by decide) (choices 1) [1,64,128] r17474 c17474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6457
  · exact u6458
  · exact u6459

def b17475 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 14 52 74 176 225 193 193 449), lower := (rows 289 14 52 74 176 32 64 128 256), losses := [] }

theorem u17475 : Upper (D 8) (R 8) [288,12,48,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17476 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 74 208 161 225 161 417), lower := (rows 289 14 52 74 208 32 64 128 256), losses := [] }

theorem u17476 : Upper (D 8) (R 8) [288,12,48,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17477 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 104 81 163 195 131 387), lower := (rows 289 14 52 104 81 32 64 128 256), losses := [] }

theorem u17477 : Upper (D 8) (R 8) [288,12,48,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17478 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 52 104 82 161 193 129 385), lower := (rows 289 14 52 104 82 32 64 128 256), losses := [] }

theorem u17478 : Upper (D 8) (R 8) [288,12,48,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17479 : Route 9 := (fun mask => (mask,id))

def c17479 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17479 : Upper (D 8) (R 8) [288,12,48,96,129] 13 := by
  apply FastRouting.sound _ _ [288,12,48,96,129] 13 (by decide) (choices 1) [1,2,64,128] r17479 c17479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6460
  · exact u6461
  · exact u6462
  · exact u6463

def r17480 : Route 9 := (fun mask => (mask,id))

def c17480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17480 : Upper (D 8) (R 8) [288,12,48,96,130] 13 := by
  apply FastRouting.sound _ _ [288,12,48,96,130] 13 (by decide) (choices 1) [1,64,128] r17480 c17480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6464
  · exact u6465
  · exact u6466

def b17481 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 104 208 163 195 131 387), lower := (rows 289 14 52 104 208 32 64 128 256), losses := [] }

theorem u17481 : Upper (D 8) (R 8) [288,12,48,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17482 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 289 14 52 200 49 227 195 195 451), lower := (rows 289 14 52 200 49 32 64 128 256), losses := [] }

theorem u17482 : Upper (D 8) (R 8) [288,12,48,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17482 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17483 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 14 52 200 50 225 193 193 449), lower := (rows 289 14 52 200 50 32 64 128 256), losses := [] }

theorem u17483 : Upper (D 8) (R 8) [288,12,48,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17484 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 200 81 163 227 163 419), lower := (rows 289 14 52 200 81 32 64 128 256), losses := [] }

theorem u17484 : Upper (D 8) (R 8) [288,12,48,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17485 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 52 200 82 161 225 161 417), lower := (rows 289 14 52 200 82 32 64 128 256), losses := [] }

theorem u17485 : Upper (D 8) (R 8) [288,12,48,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17486 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 289 14 52 200 112 163 195 131 387), lower := (rows 289 14 52 200 112 32 64 128 256), losses := [] }

theorem u17486 : Upper (D 8) (R 8) [288,12,48,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17487 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 289 14 52 200 208 35 99 163 291), lower := (rows 289 14 52 200 208 32 64 128 256), losses := [] }

theorem u17487 : Upper (D 8) (R 8) [288,12,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17488 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 69 73 50 176 240 176 432), lower := (rows 289 14 69 73 50 32 64 128 256), losses := [] }

theorem u17488 : Upper (D 8) (R 8) [288,12,65,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17488 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17489 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 69 73 146 176 240 176 432), lower := (rows 289 14 69 73 146 32 64 128 256), losses := [] }

theorem u17489 : Upper (D 8) (R 8) [288,12,65,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17490 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 69 73 176 178 242 178 434), lower := (rows 289 14 69 73 176 32 64 128 256), losses := [] }

theorem u17490 : Upper (D 8) (R 8) [288,12,65,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17491 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 69 74 145 176 240 176 432), lower := (rows 289 14 69 74 145 32 64 128 256), losses := [] }

theorem u17491 : Upper (D 8) (R 8) [288,12,65,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17491 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17492 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 69 74 176 177 241 177 433), lower := (rows 289 14 69 74 176 32 64 128 256), losses := [] }

theorem u17492 : Upper (D 8) (R 8) [288,12,65,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17493 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 88 50 161 225 161 417), lower := (rows 289 14 69 88 50 32 64 128 256), losses := [] }

theorem u17493 : Upper (D 8) (R 8) [288,12,65,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17493 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17494 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 88 145 162 226 162 418), lower := (rows 289 14 69 88 145 32 64 128 256), losses := [] }

theorem u17494 : Upper (D 8) (R 8) [288,12,65,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17495 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 88 146 161 225 161 417), lower := (rows 289 14 69 88 146 32 64 128 256), losses := [] }

theorem u17495 : Upper (D 8) (R 8) [288,12,65,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17496 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 88 176 163 227 163 419), lower := (rows 289 14 69 88 176 32 64 128 256), losses := [] }

theorem u17496 : Upper (D 8) (R 8) [288,12,65,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17497 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 104 50 177 209 145 401), lower := (rows 289 14 69 104 50 32 64 128 256), losses := [] }

theorem u17497 : Upper (D 8) (R 8) [288,12,65,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17498 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 104 145 178 242 178 434), lower := (rows 289 14 69 104 145 32 64 128 256), losses := [] }

theorem u17498 : Upper (D 8) (R 8) [288,12,65,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17498 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17499 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 104 146 177 241 177 433), lower := (rows 289 14 69 104 146 32 64 128 256), losses := [] }

theorem u17499 : Upper (D 8) (R 8) [288,12,65,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17499 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17500 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 104 176 179 211 147 403), lower := (rows 289 14 69 104 176 32 64 128 256), losses := [] }

theorem u17500 : Upper (D 8) (R 8) [288,12,65,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17501 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 14 69 137 50 240 240 240 496), lower := (rows 289 14 69 137 50 32 64 128 256), losses := [] }

theorem u17501 : Upper (D 8) (R 8) [288,12,65,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17502 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 137 82 176 240 176 432), lower := (rows 289 14 69 137 82 32 64 128 256), losses := [] }

theorem u17502 : Upper (D 8) (R 8) [288,12,65,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17503 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 14 69 137 112 178 242 178 434), lower := (rows 289 14 69 137 112 32 64 128 256), losses := [] }

theorem u17503 : Upper (D 8) (R 8) [288,12,65,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17504 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 289 14 69 137 208 50 114 178 306), lower := (rows 289 14 69 137 208 32 64 128 256), losses := [] }

theorem u17504 : Upper (D 8) (R 8) [288,12,65,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17505 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 14 69 138 49 240 240 240 496), lower := (rows 289 14 69 138 49 32 64 128 256), losses := [] }

theorem u17505 : Upper (D 8) (R 8) [288,12,65,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17506 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 69 138 81 176 240 176 432), lower := (rows 289 14 69 138 81 32 64 128 256), losses := [] }

theorem u17506 : Upper (D 8) (R 8) [288,12,65,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17507 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 138 112 177 241 177 433), lower := (rows 289 14 69 138 112 32 64 128 256), losses := [] }

theorem u17507 : Upper (D 8) (R 8) [288,12,65,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17508 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 138 145 112 112 240 368), lower := (rows 289 14 69 138 145 32 64 128 256), losses := [] }

theorem u17508 : Upper (D 8) (R 8) [288,12,65,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17509 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 138 176 113 113 241 369), lower := (rows 289 14 69 138 176 32 64 128 256), losses := [] }

theorem u17509 : Upper (D 8) (R 8) [288,12,65,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17510 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 138 208 49 113 177 305), lower := (rows 289 14 69 138 208 32 64 128 256), losses := [] }

theorem u17510 : Upper (D 8) (R 8) [288,12,65,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17511 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 289 14 69 152 49 226 226 226 482), lower := (rows 289 14 69 152 49 32 64 128 256), losses := [] }

theorem u17511 : Upper (D 8) (R 8) [288,12,65,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r17512 : Route 9 := (fun mask => (mask,id))

def c17512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17512 : Upper (D 8) (R 8) [288,12,65,144,34] 13 := by
  apply FastRouting.sound _ _ [288,12,65,144,34] 13 (by decide) (choices 1) [1,64,128] r17512 c17512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6467
  · exact u6468
  · exact u6469

def b17513 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 69 152 81 162 226 162 418), lower := (rows 289 14 69 152 81 32 64 128 256), losses := [] }

theorem u17513 : Upper (D 8) (R 8) [288,12,65,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17514 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 152 82 161 225 161 417), lower := (rows 289 14 69 152 82 32 64 128 256), losses := [] }

theorem u17514 : Upper (D 8) (R 8) [288,12,65,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17515 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 152 112 163 227 163 419), lower := (rows 289 14 69 152 112 32 64 128 256), losses := [] }

theorem u17515 : Upper (D 8) (R 8) [288,12,65,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17516 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 152 145 98 98 226 354), lower := (rows 289 14 69 152 145 32 64 128 256), losses := [] }

theorem u17516 : Upper (D 8) (R 8) [288,12,65,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17517 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 152 146 97 97 225 353), lower := (rows 289 14 69 152 146 32 64 128 256), losses := [] }

theorem u17517 : Upper (D 8) (R 8) [288,12,65,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17518 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 152 176 99 99 227 355), lower := (rows 289 14 69 152 176 32 64 128 256), losses := [] }

theorem u17518 : Upper (D 8) (R 8) [288,12,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17519 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 289 14 69 152 208 35 99 163 291), lower := (rows 289 14 69 152 208 32 64 128 256), losses := [] }

theorem u17519 : Upper (D 8) (R 8) [288,12,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u17519
end Delivery.IrregularNine14.P08
