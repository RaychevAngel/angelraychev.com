import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0350
import IrregularNine14P06C0351

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r36540 : Route 9 := (fun mask => (mask,id))

def c36540 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u36540 : Upper (D 6) (R 6) [34,72,129,17,36] 13 := by
  apply FastRouting.sound _ _ [34,72,129,17,36] 13 (by decide) (choices 1) [2,4,64,256] r36540 c36540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21037
  · exact u21038
  · exact u21039
  · exact u21040

def b36541 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 133 25 82 292 356 420 292), lower := (rows 35 74 133 25 82 32 64 128 256), losses := [] }

theorem u36541 : Upper (D 6) (R 6) [34,72,129,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36542 : Route 9 := (fun mask => (mask,id))

def c36542 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36542 : Upper (D 6) (R 6) [34,72,129,17,68] 13 := by
  apply FastRouting.sound _ _ [34,72,129,17,68] 13 (by decide) (choices 1) [2,4,256] r36542 c36542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21041
  · exact u21042
  · exact u21043

def b36543 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 133 25 112 294 326 390 262), lower := (rows 35 74 133 25 112 32 64 128 256), losses := [] }

theorem u36543 : Upper (D 6) (R 6) [34,72,129,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36544 : Route 9 := (fun mask => (mask,id))

def c36544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36544 : Upper (D 6) (R 6) [34,72,129,17,258] 13 := by
  apply FastRouting.sound _ _ [34,72,129,17,258] 13 (by decide) (choices 1) [4,64] r36544 c36544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21044
  · exact u21045

def r36545 : Route 9 := (fun mask => (mask,id))

def c36545 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36545 : Upper (D 6) (R 6) [34,72,129,17,260] 13 := by
  apply FastRouting.sound _ _ [34,72,129,17,260] 13 (by decide) (choices 1) [2,4,64] r36545 c36545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21046
  · exact u21047
  · exact u21048

def r36546 : Route 9 := (fun mask => (mask,id))

def c36546 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36546 : Upper (D 6) (R 6) [34,72,129,17,288] 13 := by
  apply FastRouting.sound _ _ [34,72,129,17,288] 13 (by decide) (choices 1) [2,4,64] r36546 c36546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21049
  · exact u21050
  · exact u21051

def r36547 : Route 9 := (fun mask => (mask,id))

def c36547 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36547 : Upper (D 6) (R 6) [34,72,129,17,320] 13 := by
  apply FastRouting.sound _ _ [34,72,129,17,320] 13 (by decide) (choices 1) [2,4] r36547 c36547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21052
  · exact u21053

def b36548 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 2, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 35 74 133 26 21 356 356 484 356), lower := (rows 35 74 133 26 21 32 64 128 256), losses := [] }

theorem u36548 : Upper (D 6) (R 6) [34,72,129,18,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36549 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 133 26 49 356 324 452 324), lower := (rows 35 74 133 26 49 32 64 128 256), losses := [] }

theorem u36549 : Upper (D 6) (R 6) [34,72,129,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36550 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 452, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 35 74 133 26 52 357 325 453 325), lower := (rows 35 74 133 26 52 32 64 128 256), losses := [] }

theorem u36550 : Upper (D 6) (R 6) [34,72,129,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36551 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 133 26 81 292 356 420 292), lower := (rows 35 74 133 26 81 32 64 128 256), losses := [] }

theorem u36551 : Upper (D 6) (R 6) [34,72,129,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36552 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 133 26 84 293 357 421 293), lower := (rows 35 74 133 26 84 32 64 128 256), losses := [] }

theorem u36552 : Upper (D 6) (R 6) [34,72,129,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36553 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 133 26 112 293 325 389 261), lower := (rows 35 74 133 26 112 32 64 128 256), losses := [] }

theorem u36553 : Upper (D 6) (R 6) [34,72,129,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36554 : Route 9 := (fun mask => (mask,id))

def c36554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36554 : Upper (D 6) (R 6) [34,72,129,18,257] 13 := by
  apply FastRouting.sound _ _ [34,72,129,18,257] 13 (by decide) (choices 1) [4,64] r36554 c36554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21054
  · exact u21055

def r36555 : Route 9 := (fun mask => (mask,id))

def c36555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36555 : Upper (D 6) (R 6) [34,72,129,18,260] 13 := by
  apply FastRouting.sound _ _ [34,72,129,18,260] 13 (by decide) (choices 1) [1,4,64] r36555 c36555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21056
  · exact u21057
  · exact u21058

def b36556 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 35 74 133 26 304 101 69 197 325), lower := (rows 35 74 133 26 304 32 64 128 256), losses := [] }

theorem u36556 : Upper (D 6) (R 6) [34,72,129,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36557 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 133 26 336 37 101 165 293), lower := (rows 35 74 133 26 336 32 64 128 256), losses := [] }

theorem u36557 : Upper (D 6) (R 6) [34,72,129,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36558 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 74 133 28 19 356 356 484 356), lower := (rows 35 74 133 28 19 32 64 128 256), losses := [] }

theorem u36558 : Upper (D 6) (R 6) [34,72,129,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36559 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 74 133 28 21 354 354 482 354), lower := (rows 35 74 133 28 21 32 64 128 256), losses := [] }

theorem u36559 : Upper (D 6) (R 6) [34,72,129,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36560 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 133 28 22 353 353 481 353), lower := (rows 35 74 133 28 22 32 64 128 256), losses := [] }

theorem u36560 : Upper (D 6) (R 6) [34,72,129,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36561 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 74 133 28 49 358 326 454 326), lower := (rows 35 74 133 28 49 32 64 128 256), losses := [] }

theorem u36561 : Upper (D 6) (R 6) [34,72,129,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36562 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 133 28 50 357 325 453 325), lower := (rows 35 74 133 28 50 32 64 128 256), losses := [] }

theorem u36562 : Upper (D 6) (R 6) [34,72,129,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36563 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 133 28 52 355 323 451 323), lower := (rows 35 74 133 28 52 32 64 128 256), losses := [] }

theorem u36563 : Upper (D 6) (R 6) [34,72,129,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36564 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 3, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 35 74 133 28 81 294 358 422 294), lower := (rows 35 74 133 28 81 32 64 128 256), losses := [] }

theorem u36564 : Upper (D 6) (R 6) [34,72,129,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36565 : PairBound 9 := { available := 293, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 133 28 82 293 357 421 293), lower := (rows 35 74 133 28 82 32 64 128 256), losses := [] }

theorem u36565 : Upper (D 6) (R 6) [34,72,129,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36566 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 10, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 133 28 84 291 355 419 291), lower := (rows 35 74 133 28 84 32 64 128 256), losses := [] }

theorem u36566 : Upper (D 6) (R 6) [34,72,129,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36567 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 388, targets := 32 }], pairs := [(0,6),(2,5),(2,6)], upper := (rows 35 74 133 28 112 295 327 391 263), lower := (rows 35 74 133 28 112 32 64 128 256), losses := [] }

theorem u36567 : Upper (D 6) (R 6) [34,72,129,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36568 : Route 9 := (fun mask => (mask,id))

def c36568 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36568 : Upper (D 6) (R 6) [34,72,129,20,257] 13 := by
  apply FastRouting.sound _ _ [34,72,129,20,257] 13 (by decide) (choices 1) [2,4,64] r36568 c36568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21059
  · exact u21060
  · exact u21061

def r36569 : Route 9 := (fun mask => (mask,id))

def c36569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36569 : Upper (D 6) (R 6) [34,72,129,20,258] 13 := by
  apply FastRouting.sound _ _ [34,72,129,20,258] 13 (by decide) (choices 1) [1,4,64] r36569 c36569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21062
  · exact u21063
  · exact u21064

def b36570 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 74 133 28 276 99 99 227 355), lower := (rows 35 74 133 28 276 32 64 128 256), losses := [] }

theorem u36570 : Upper (D 6) (R 6) [34,72,129,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36571 : Route 9 := (fun mask => (mask,id))

def c36571 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36571 : Upper (D 6) (R 6) [34,72,129,20,288] 13 := by
  apply FastRouting.sound _ _ [34,72,129,20,288] 13 (by decide) (choices 1) [1,2,4,64] r36571 c36571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21065
  · exact u21066
  · exact u21067
  · exact u21068

def r36572 : Route 9 := (fun mask => (mask,id))

def c36572 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36572 : Upper (D 6) (R 6) [34,72,129,20,320] 13 := by
  apply FastRouting.sound _ _ [34,72,129,20,320] 13 (by decide) (choices 1) [1,2,4] r36572 c36572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21069
  · exact u21070
  · exact u21071

def b36573 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 74 133 44 19 372 340 468 340), lower := (rows 35 74 133 44 19 32 64 128 256), losses := [] }

theorem u36573 : Upper (D 6) (R 6) [34,72,129,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36574 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 74 133 44 21 370 338 466 338), lower := (rows 35 74 133 44 21 32 64 128 256), losses := [] }

theorem u36574 : Upper (D 6) (R 6) [34,72,129,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36575 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 353, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 133 44 22 369 337 465 337), lower := (rows 35 74 133 44 22 32 64 128 256), losses := [] }

theorem u36575 : Upper (D 6) (R 6) [34,72,129,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36576 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 74 133 44 81 310 342 406 278), lower := (rows 35 74 133 44 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 21 8 21 0 73 137 265), good := (rows 471 458 469 478 469 0 64 128 256) }] }

theorem u36576 : Upper (D 6) (R 6) [34,72,129,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36577 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 133 44 82 309 341 405 277), lower := (rows 35 74 133 44 82 32 64 128 256), losses := [] }

theorem u36577 : Upper (D 6) (R 6) [34,72,129,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36578 : Route 9 := (fun mask => (mask,id))

def c36578 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u36578 : Upper (D 6) (R 6) [34,72,129,36,68] 13 := by
  apply FastRouting.sound _ _ [34,72,129,36,68] 13 (by decide) (choices 1) [1,2,16,256] r36578 c36578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21072
  · exact u21073
  · exact u21074
  · exact u21075

def b36579 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 74 133 44 273 118 86 214 342), lower := (rows 35 74 133 44 273 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 21 8 21 0 73 137 265), good := (rows 471 458 469 478 469 0 64 128 256) }] }

theorem u36579 : Upper (D 6) (R 6) [34,72,129,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36580 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 74 133 44 274 117 85 213 341), lower := (rows 35 74 133 44 274 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 5 8 25 0 69 133 261), good := (rows 471 90 469 478 274 0 64 128 256) }] }

theorem u36580 : Upper (D 6) (R 6) [34,72,129,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36581 : Route 9 := (fun mask => (mask,id))

def c36581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36581 : Upper (D 6) (R 6) [34,72,129,36,260] 13 := by
  apply FastRouting.sound _ _ [34,72,129,36,260] 13 (by decide) (choices 1) [1,2,16,64] r36581 c36581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21076
  · exact u21077
  · exact u21078
  · exact u21079

def r36582 : Route 9 := (fun mask => (mask,id))

def c36582 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36582 : Upper (D 6) (R 6) [34,72,129,36,320] 13 := by
  apply FastRouting.sound _ _ [34,72,129,36,320] 13 (by decide) (choices 1) [1,2,4,16] r36582 c36582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21080
  · exact u21081
  · exact u21082
  · exact u21083

def b36583 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 74 133 56 19 356 324 452 324), lower := (rows 35 74 133 56 19 32 64 128 256), losses := [] }

theorem u36583 : Upper (D 6) (R 6) [34,72,129,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36584 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 74 133 56 21 358 326 454 326), lower := (rows 35 74 133 56 21 32 64 128 256), losses := [] }

theorem u36584 : Upper (D 6) (R 6) [34,72,129,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36585 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 35 74 133 56 22 357 325 453 325), lower := (rows 35 74 133 56 22 32 64 128 256), losses := [] }

theorem u36585 : Upper (D 6) (R 6) [34,72,129,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36586 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 133 56 81 294 326 390 262), lower := (rows 35 74 133 56 81 32 64 128 256), losses := [] }

theorem u36586 : Upper (D 6) (R 6) [34,72,129,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36587 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 133 56 82 293 325 389 261), lower := (rows 35 74 133 56 82 32 64 128 256), losses := [] }

theorem u36587 : Upper (D 6) (R 6) [34,72,129,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36588 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 133 56 84 295 327 391 263), lower := (rows 35 74 133 56 84 32 64 128 256), losses := [] }

theorem u36588 : Upper (D 6) (R 6) [34,72,129,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36589 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 74 133 56 273 102 70 198 326), lower := (rows 35 74 133 56 273 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 21 8 21 0 73 137 265), good := (rows 471 458 469 478 469 0 64 128 256) }] }

theorem u36589 : Upper (D 6) (R 6) [34,72,129,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b36590 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 35 74 133 56 274 101 69 197 325), lower := (rows 35 74 133 56 274 32 64 128 256), losses := [] }

theorem u36590 : Upper (D 6) (R 6) [34,72,129,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36591 : Route 9 := (fun mask => (mask,id))

def c36591 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36591 : Upper (D 6) (R 6) [34,72,129,48,260] 13 := by
  apply FastRouting.sound _ _ [34,72,129,48,260] 13 (by decide) (choices 1) [1,2,4,64] r36591 c36591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21084
  · exact u21085
  · exact u21086
  · exact u21087

def b36592 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 133 56 336 39 71 135 263), lower := (rows 35 74 133 56 336 32 64 128 256), losses := [] }

theorem u36592 : Upper (D 6) (R 6) [34,72,129,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36593 : Route 9 := (fun mask => (mask,id))

def c36593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36593 : Upper (D 6) (R 6) [34,72,129,257,6] 13 := by
  apply FastRouting.sound _ _ [34,72,129,257,6] 13 (by decide) (choices 1) [4,16,64] r36593 c36593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21088
  · exact u21089
  · exact u21090

def b36594 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 74 133 265 50 116 84 212 340), lower := (rows 35 74 133 265 50 32 64 128 256), losses := [] }

theorem u36594 : Upper (D 6) (R 6) [34,72,129,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36595 : Route 9 := (fun mask => (mask,id))

def c36595 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36595 : Upper (D 6) (R 6) [34,72,129,257,36] 13 := by
  apply FastRouting.sound _ _ [34,72,129,257,36] 13 (by decide) (choices 1) [2,4,16,64] r36595 c36595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21091
  · exact u21092
  · exact u21093
  · exact u21094

def b36596 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 74 133 265 82 52 116 180 308), lower := (rows 35 74 133 265 82 32 64 128 256), losses := [] }

theorem u36596 : Upper (D 6) (R 6) [34,72,129,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r36597 : Route 9 := (fun mask => (mask,id))

def c36597 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36597 : Upper (D 6) (R 6) [34,72,129,257,68] 13 := by
  apply FastRouting.sound _ _ [34,72,129,257,68] 13 (by decide) (choices 1) [2,4,16] r36597 c36597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21095
  · exact u21096
  · exact u21097

def r36598 : Route 9 := (fun mask => (mask,id))

def c36598 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u36598 : Upper (D 6) (R 6) [34,72,129,257,96] 13 := by
  apply FastRouting.sound _ _ [34,72,129,257,96] 13 (by decide) (choices 1) [2,4,16] r36598 c36598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21098
  · exact u21099
  · exact u21100

def b36599 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 2, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 35 74 133 266 21 116 116 244 372), lower := (rows 35 74 133 266 21 32 64 128 256), losses := [] }

theorem u36599 : Upper (D 6) (R 6) [34,72,129,258,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b36599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u36599
end Delivery.IrregularNine14.P06
