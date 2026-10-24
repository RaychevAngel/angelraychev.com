import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0079
import IrregularNine14P06C0080

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17460 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 70 268 52 48 65 193 321), lower := (rows 11 162 70 268 52 48 64 128 256), losses := [] }

theorem u17460 : Upper (D 6) (R 6) [10,160,66,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17460 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17461 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 70 268 52 96 81 145 273), lower := (rows 11 162 70 268 52 96 64 128 256), losses := [] }

theorem u17461 : Upper (D 6) (R 6) [10,160,66,260,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17462 : Route 9 := (fun mask => (mask,id))

def c17462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17462 : Upper (D 6) (R 6) [10,160,66,260,65,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,65,1] 13 (by decide) (choices 1) [4,16,32] r17462 c17462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4756
  · exact u4757
  · exact u4758

def r17463 : Route 9 := (fun mask => (mask,id))

def c17463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17463 : Upper (D 6) (R 6) [10,160,66,260,65,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,65,4] 13 (by decide) (choices 1) [1,16,32] r17463 c17463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4759
  · exact u4760
  · exact u4761

def r17464 : Route 9 := (fun mask => (mask,id))

def c17464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17464 : Upper (D 6) (R 6) [10,160,66,260,65,16] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,65,16] 13 (by decide) (choices 1) [1,4,32] r17464 c17464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4762
  · exact u4763
  · exact u4764

def r17465 : Route 9 := (fun mask => (mask,id))

def c17465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17465 : Upper (D 6) (R 6) [10,160,66,260,96,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,96,1] 13 (by decide) (choices 1) [1,4,16] r17465 c17465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4765
  · exact u4766
  · exact u4767

def r17466 : Route 9 := (fun mask => (mask,id))

def c17466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17466 : Upper (D 6) (R 6) [10,160,66,260,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,260,96,4] 13 (by decide) (choices 1) [1,16] r17466 c17466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4768
  · exact u4769

def b17467 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 70 268 112 48 69 133 261), lower := (rows 11 162 70 268 112 48 64 128 256), losses := [] }

theorem u17467 : Upper (D 6) (R 6) [10,160,66,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17467 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17468 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 162 70 280 21 33 100 228 356), lower := (rows 11 162 70 280 21 33 64 128 256), losses := [] }

theorem u17468 : Upper (D 6) (R 6) [10,160,66,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17469 : Route 9 := (fun mask => (mask,id))

def c17469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17469 : Upper (D 6) (R 6) [10,160,66,272,5,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,5,4] 13 (by decide) (choices 1) [1,32] r17469 c17469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4770
  · exact u4771

def r17470 : Route 9 := (fun mask => (mask,id))

def c17470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17470 : Upper (D 6) (R 6) [10,160,66,272,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,5,64] 13 (by decide) (choices 1) [1,4,32] r17470 c17470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4772
  · exact u4773
  · exact u4774

def b17471 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 70 280 49 33 68 196 324), lower := (rows 11 162 70 280 49 33 64 128 256), losses := [] }

theorem u17471 : Upper (D 6) (R 6) [10,160,66,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17472 : Route 9 := (fun mask => (mask,id))

def c17472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17472 : Upper (D 6) (R 6) [10,160,66,272,33,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,33,4] 13 (by decide) (choices 1) [1,4] r17472 c17472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4775
  · exact u4776

def r17473 : Route 9 := (fun mask => (mask,id))

def c17473 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17473 : Upper (D 6) (R 6) [10,160,66,272,33,64] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,33,64] 13 (by decide) (choices 1) [1,4] r17473 c17473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4777
  · exact u4778

def r17474 : Route 9 := (fun mask => (mask,id))

def c17474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17474 : Upper (D 6) (R 6) [10,160,66,272,36,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,36,1] 13 (by decide) (choices 1) [1,4] r17474 c17474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4779
  · exact u4780

def b17475 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 162 70 280 52 36 65 193 321), lower := (rows 11 162 70 280 52 36 64 128 256), losses := [] }

theorem u17475 : Upper (D 6) (R 6) [10,160,66,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17476 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 70 280 52 96 69 133 261), lower := (rows 11 162 70 280 52 96 64 128 256), losses := [] }

theorem u17476 : Upper (D 6) (R 6) [10,160,66,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17477 : Route 9 := (fun mask => (mask,id))

def c17477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17477 : Upper (D 6) (R 6) [10,160,66,272,65,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,65,1] 13 (by decide) (choices 1) [4,32] r17477 c17477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4781
  · exact u4782

def r17478 : Route 9 := (fun mask => (mask,id))

def c17478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17478 : Upper (D 6) (R 6) [10,160,66,272,65,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,65,4] 13 (by decide) (choices 1) [1,4,32] r17478 c17478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4783
  · exact u4784
  · exact u4785

def r17479 : Route 9 := (fun mask => (mask,id))

def c17479 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17479 : Upper (D 6) (R 6) [10,160,66,272,96,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,272,96,1] 13 (by decide) (choices 1) [1,4] r17479 c17479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4786
  · exact u4787

def b17480 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 162 70 280 112 36 69 133 261), lower := (rows 11 162 70 280 112 36 64 128 256), losses := [] }

theorem u17480 : Upper (D 6) (R 6) [10,160,66,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17481 : Route 9 := (fun mask => (mask,id))

def c17481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17481 : Upper (D 6) (R 6) [10,160,66,288,65,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,288,65,1] 13 (by decide) (choices 1) [4,16] r17481 c17481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4788
  · exact u4789

def r17482 : Route 9 := (fun mask => (mask,id))

def c17482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17482 : Upper (D 6) (R 6) [10,160,66,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,288,65,4] 13 (by decide) (choices 1) [1,4,16] r17482 c17482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4790
  · exact u4791
  · exact u4792

def b17483 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 296 81 48 69 133 261), lower := (rows 11 162 70 296 81 48 64 128 256), losses := [] }

theorem u17483 : Upper (D 6) (R 6) [10,160,66,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17483 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17484 : Route 9 := (fun mask => (mask,id))

def c17484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17484 : Upper (D 6) (R 6) [10,160,66,320,5,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,320,5,1] 13 (by decide) (choices 1) [4,16,32] r17484 c17484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4793
  · exact u4794
  · exact u4795

def r17485 : Route 9 := (fun mask => (mask,id))

def c17485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17485 : Upper (D 6) (R 6) [10,160,66,320,5,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,320,5,4] 13 (by decide) (choices 1) [1,16,32] r17485 c17485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4796
  · exact u4797
  · exact u4798

def b17486 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6),(3,1)], upper := (rows 11 162 70 328 21 48 101 165 293), lower := (rows 11 162 70 328 21 48 64 128 256), losses := [] }

theorem u17486 : Upper (D 6) (R 6) [10,160,66,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17486 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17487 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 70 328 49 33 84 148 276), lower := (rows 11 162 70 328 49 33 64 128 256), losses := [] }

theorem u17487 : Upper (D 6) (R 6) [10,160,66,320,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17488 : Route 9 := (fun mask => (mask,id))

def c17488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17488 : Upper (D 6) (R 6) [10,160,66,320,33,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,320,33,4] 13 (by decide) (choices 1) [1,4,16] r17488 c17488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4799
  · exact u4800
  · exact u4801

def b17489 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 162 70 328 49 48 69 133 261), lower := (rows 11 162 70 328 49 48 64 128 256), losses := [] }

theorem u17489 : Upper (D 6) (R 6) [10,160,66,320,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17489 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17490 : Route 9 := (fun mask => (mask,id))

def c17490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17490 : Upper (D 6) (R 6) [10,160,66,320,36,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,320,36,1] 13 (by decide) (choices 1) [1,4,16] r17490 c17490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4802
  · exact u4803
  · exact u4804

def b17491 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 162 70 328 52 36 81 145 273), lower := (rows 11 162 70 328 52 36 64 128 256), losses := [] }

theorem u17491 : Upper (D 6) (R 6) [10,160,66,320,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17492 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 70 328 52 48 69 133 261), lower := (rows 11 162 70 328 52 48 64 128 256), losses := [] }

theorem u17492 : Upper (D 6) (R 6) [10,160,66,320,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17492 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17493 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 84 13 49 34 324 452 324), lower := (rows 11 162 84 13 49 34 64 128 256), losses := [] }

theorem u17493 : Upper (D 6) (R 6) [10,160,80,5,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17494 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 4, region := 450, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 162 84 13 49 36 322 450 322), lower := (rows 11 162 84 13 49 36 64 128 256), losses := [] }

theorem u17494 : Upper (D 6) (R 6) [10,160,80,5,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17495 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 454, targets := 1 }], pairs := [(1,0),(2,0),(4,1)], upper := (rows 11 162 84 13 49 96 326 390 262), lower := (rows 11 162 84 13 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 100 64 128 256), good := (rows 25 160 116 61 49 96 96 128 256) }] }

theorem u17495 : Upper (D 6) (R 6) [10,160,80,5,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17496 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 84 13 49 288 70 198 326), lower := (rows 11 162 84 13 49 288 64 128 256), losses := [] }

theorem u17496 : Upper (D 6) (R 6) [10,160,80,5,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17496 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17497 : PairBound 9 := { available := 322, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 13 52 33 322 450 322), lower := (rows 11 162 84 13 52 33 64 128 256), losses := [] }

theorem u17497 : Upper (D 6) (R 6) [10,160,80,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17498 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 13 52 34 321 449 321), lower := (rows 11 162 84 13 52 34 64 128 256), losses := [] }

theorem u17498 : Upper (D 6) (R 6) [10,160,80,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17499 : PairBound 9 := { available := 259, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 84 13 52 96 323 387 259), lower := (rows 11 162 84 13 52 96 64 128 256), losses := [] }

theorem u17499 : Upper (D 6) (R 6) [10,160,80,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17500 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 483, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 162 84 13 52 288 67 195 323), lower := (rows 11 162 84 13 52 288 64 128 256), losses := [] }

theorem u17500 : Upper (D 6) (R 6) [10,160,80,5,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17500 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17501 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 13 273 34 100 228 356), lower := (rows 11 162 84 13 273 34 64 128 256), losses := [] }

theorem u17501 : Upper (D 6) (R 6) [10,160,80,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17502 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 5, region := 194, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 162 84 13 273 36 98 226 354), lower := (rows 11 162 84 13 273 36 64 128 256), losses := [] }

theorem u17502 : Upper (D 6) (R 6) [10,160,80,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17503 : Route 9 := (fun mask => (mask,id))

def c17503 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17503 : Upper (D 6) (R 6) [10,160,80,5,257,64] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,257,64] 13 (by decide) (choices 1) [2,4,32] r17503 c17503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4805
  · exact u4806
  · exact u4807

def b17504 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 13 274 33 100 228 356), lower := (rows 11 162 84 13 274 33 64 128 256), losses := [] }

theorem u17504 : Upper (D 6) (R 6) [10,160,80,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17505 : Route 9 := (fun mask => (mask,id))

def c17505 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17505 : Upper (D 6) (R 6) [10,160,80,5,258,4] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,258,4] 13 (by decide) (choices 1) [1,32] r17505 c17505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4808
  · exact u4809

def r17506 : Route 9 := (fun mask => (mask,id))

def c17506 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17506 : Upper (D 6) (R 6) [10,160,80,5,258,64] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,258,64] 13 (by decide) (choices 1) [1,4,32] r17506 c17506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4810
  · exact u4811
  · exact u4812

def b17507 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 13 276 33 98 226 354), lower := (rows 11 162 84 13 276 33 64 128 256), losses := [] }

theorem u17507 : Upper (D 6) (R 6) [10,160,80,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17508 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 13 276 34 97 225 353), lower := (rows 11 162 84 13 276 34 64 128 256), losses := [] }

theorem u17508 : Upper (D 6) (R 6) [10,160,80,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17509 : Route 9 := (fun mask => (mask,id))

def c17509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17509 : Upper (D 6) (R 6) [10,160,80,5,260,64] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,260,64] 13 (by decide) (choices 1) [1,2,32] r17509 c17509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4813
  · exact u4814
  · exact u4815

def b17510 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 13 304 33 70 198 326), lower := (rows 11 162 84 13 304 33 64 128 256), losses := [] }

theorem u17510 : Upper (D 6) (R 6) [10,160,80,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17511 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 84 13 304 34 69 197 325), lower := (rows 11 162 84 13 304 34 64 128 256), losses := [] }

theorem u17511 : Upper (D 6) (R 6) [10,160,80,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17512 : Route 9 := (fun mask => (mask,id))

def c17512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17512 : Upper (D 6) (R 6) [10,160,80,5,288,4] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,288,4] 13 (by decide) (choices 1) [1,2] r17512 c17512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4816
  · exact u4817

def r17513 : Route 9 := (fun mask => (mask,id))

def c17513 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17513 : Upper (D 6) (R 6) [10,160,80,5,288,64] 13 := by
  apply FastRouting.sound _ _ [10,160,80,5,288,64] 13 (by decide) (choices 1) [1,2,4] r17513 c17513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4818
  · exact u4819
  · exact u4820

def b17514 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 84 44 273 33 70 198 326), lower := (rows 11 162 84 44 273 33 64 128 256), losses := [] }

theorem u17514 : Upper (D 6) (R 6) [10,160,80,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17515 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 84 44 273 34 69 197 325), lower := (rows 11 162 84 44 273 34 64 128 256), losses := [] }

theorem u17515 : Upper (D 6) (R 6) [10,160,80,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17515 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17516 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 84 44 273 36 67 195 323), lower := (rows 11 162 84 44 273 36 64 128 256), losses := [] }

theorem u17516 : Upper (D 6) (R 6) [10,160,80,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17517 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 162 84 44 273 96 71 135 263), lower := (rows 11 162 84 44 273 96 64 128 256), losses := [] }

theorem u17517 : Upper (D 6) (R 6) [10,160,80,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17518 : Route 9 := (fun mask => (mask,id))

def c17518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17518 : Upper (D 6) (R 6) [10,160,80,36,258,1] 13 := by
  apply FastRouting.sound _ _ [10,160,80,36,258,1] 13 (by decide) (choices 1) [1,4] r17518 c17518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4821
  · exact u4822

def b17519 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 162 84 44 274 36 65 193 321), lower := (rows 11 162 84 44 274 36 64 128 256), losses := [] }

theorem u17519 : Upper (D 6) (R 6) [10,160,80,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u17519
end Delivery.IrregularNine14.P06
