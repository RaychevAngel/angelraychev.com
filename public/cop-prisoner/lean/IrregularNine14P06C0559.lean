import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0277
import IrregularNine14P06C0278

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33540 : Route 9 := (fun mask => (mask,id))

def c33540 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33540 : Upper (D 6) (R 6) [10,144,33,68,320] 13 := by
  apply FastRouting.sound _ _ [10,144,33,68,320] 13 (by decide) (choices 1) [1,2,4] r33540 c33540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16653
  · exact u16654
  · exact u16655

def b33541 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 37 104 19 356 324 452 324), lower := (rows 11 146 37 104 19 32 64 128 256), losses := [] }

theorem u33541 : Upper (D 6) (R 6) [10,144,33,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33542 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 11 146 37 104 21 358 326 454 326), lower := (rows 11 146 37 104 21 32 64 128 256), losses := [] }

theorem u33542 : Upper (D 6) (R 6) [10,144,33,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33543 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 146 37 104 22 357 325 453 325), lower := (rows 11 146 37 104 22 32 64 128 256), losses := [] }

theorem u33543 : Upper (D 6) (R 6) [10,144,33,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33544 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 146 37 104 81 294 326 390 262), lower := (rows 11 146 37 104 81 32 64 128 256), losses := [] }

theorem u33544 : Upper (D 6) (R 6) [10,144,33,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33545 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 146 37 104 82 293 325 389 261), lower := (rows 11 146 37 104 82 32 64 128 256), losses := [] }

theorem u33545 : Upper (D 6) (R 6) [10,144,33,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33546 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 292, targets := 64 }], pairs := [(1,5),(2,6),(4,5)], upper := (rows 11 146 37 104 84 295 327 391 263), lower := (rows 11 146 37 104 84 32 64 128 256), losses := [] }

theorem u33546 : Upper (D 6) (R 6) [10,144,33,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33547 : Route 9 := (fun mask => (mask,id))

def c33547 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33547 : Upper (D 6) (R 6) [10,144,33,96,257] 13 := by
  apply FastRouting.sound _ _ [10,144,33,96,257] 13 (by decide) (choices 1) [2,4,64] r33547 c33547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16656
  · exact u16657
  · exact u16658

def b33548 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 108, targets := 2 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 146 37 104 274 101 69 197 325), lower := (rows 11 146 37 104 274 32 64 128 256), losses := [] }

theorem u33548 : Upper (D 6) (R 6) [10,144,33,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33549 : Route 9 := (fun mask => (mask,id))

def c33549 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33549 : Upper (D 6) (R 6) [10,144,33,96,260] 13 := by
  apply FastRouting.sound _ _ [10,144,33,96,260] 13 (by decide) (choices 1) [1,2,4,64] r33549 c33549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16659
  · exact u16660
  · exact u16661
  · exact u16662

def b33550 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 36, targets := 64 }], pairs := [(1,5),(2,6),(4,5)], upper := (rows 11 146 37 104 336 39 71 135 263), lower := (rows 11 146 37 104 336 32 64 128 256), losses := [] }

theorem u33550 : Upper (D 6) (R 6) [10,144,33,96,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33551 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 146 37 265 22 100 100 228 356), lower := (rows 11 146 37 265 22 32 64 128 256), losses := [] }

theorem u33551 : Upper (D 6) (R 6) [10,144,33,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33552 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 146 37 265 50 100 68 196 324), lower := (rows 11 146 37 265 50 32 64 128 256), losses := [] }

theorem u33552 : Upper (D 6) (R 6) [10,144,33,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33553 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 146 37 265 52 102 70 198 326), lower := (rows 11 146 37 265 52 32 64 128 256), losses := [] }

theorem u33553 : Upper (D 6) (R 6) [10,144,33,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33554 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 146 37 265 82 100 100 228 356), lower := (rows 11 146 37 265 82 32 64 128 256), losses := [] }

theorem u33554 : Upper (D 6) (R 6) [10,144,33,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33555 : Route 9 := (fun mask => (mask,id))

def c33555 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33555 : Upper (D 6) (R 6) [10,144,33,257,68] 13 := by
  apply FastRouting.sound _ _ [10,144,33,257,68] 13 (by decide) (choices 1) [2,4,64] r33555 c33555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16663
  · exact u16664
  · exact u16665

def r33556 : Route 9 := (fun mask => (mask,id))

def c33556 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33556 : Upper (D 6) (R 6) [10,144,33,257,96] 13 := by
  apply FastRouting.sound _ _ [10,144,33,257,96] 13 (by decide) (choices 1) [2,4,64] r33556 c33556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16666
  · exact u16667
  · exact u16668

def b33557 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 37 268 19 100 100 228 356), lower := (rows 11 146 37 268 19 32 64 128 256), losses := [] }

theorem u33557 : Upper (D 6) (R 6) [10,144,33,260,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33558 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 146 37 268 21 98 98 226 354), lower := (rows 11 146 37 268 21 32 64 128 256), losses := [] }

theorem u33558 : Upper (D 6) (R 6) [10,144,33,260,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33559 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(1,2),(2,1),(3,1)], upper := (rows 11 146 37 268 22 97 97 225 353), lower := (rows 11 146 37 268 22 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 37 69 133 261), good := (rows 491 146 481 488 498 32 64 128 256) }] }

theorem u33559 : Upper (D 6) (R 6) [10,144,33,260,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33560 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 11 146 37 268 49 102 70 198 326), lower := (rows 11 146 37 268 49 32 64 128 256), losses := [] }

theorem u33560 : Upper (D 6) (R 6) [10,144,33,260,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33561 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 328, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 11 146 37 268 50 101 69 197 325), lower := (rows 11 146 37 268 50 32 64 128 256), losses := [] }

theorem u33561 : Upper (D 6) (R 6) [10,144,33,260,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33562 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 37 268 52 99 67 195 323), lower := (rows 11 146 37 268 52 32 64 128 256), losses := [] }

theorem u33562 : Upper (D 6) (R 6) [10,144,33,260,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33563 : Route 9 := (fun mask => (mask,id))

def c33563 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33563 : Upper (D 6) (R 6) [10,144,33,260,65] 13 := by
  apply FastRouting.sound _ _ [10,144,33,260,65] 13 (by decide) (choices 1) [2,4,64] r33563 c33563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16669
  · exact u16670
  · exact u16671

def r33564 : Route 9 := (fun mask => (mask,id))

def c33564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33564 : Upper (D 6) (R 6) [10,144,33,260,66] 13 := by
  apply FastRouting.sound _ _ [10,144,33,260,66] 13 (by decide) (choices 1) [1,4,64] r33564 c33564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16672
  · exact u16673
  · exact u16674

def r33565 : Route 9 := (fun mask => (mask,id))

def c33565 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33565 : Upper (D 6) (R 6) [10,144,33,260,68] 13 := by
  apply FastRouting.sound _ _ [10,144,33,260,68] 13 (by decide) (choices 1) [1,2,64] r33565 c33565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16675
  · exact u16676
  · exact u16677

def r33566 : Route 9 := (fun mask => (mask,id))

def c33566 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33566 : Upper (D 6) (R 6) [10,144,33,260,96] 13 := by
  apply FastRouting.sound _ _ [10,144,33,260,96] 13 (by decide) (choices 1) [1,2,4,64] r33566 c33566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16678
  · exact u16679
  · exact u16680
  · exact u16681

def b33567 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 37 296 19 100 68 196 324), lower := (rows 11 146 37 296 19 32 64 128 256), losses := [] }

theorem u33567 : Upper (D 6) (R 6) [10,144,33,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33568 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 11 146 37 296 21 102 70 198 326), lower := (rows 11 146 37 296 21 32 64 128 256), losses := [] }

theorem u33568 : Upper (D 6) (R 6) [10,144,33,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33569 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 146 37 296 22 101 69 197 325), lower := (rows 11 146 37 296 22 32 64 128 256), losses := [] }

theorem u33569 : Upper (D 6) (R 6) [10,144,33,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33570 : Route 9 := (fun mask => (mask,id))

def c33570 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33570 : Upper (D 6) (R 6) [10,144,33,288,65] 13 := by
  apply FastRouting.sound _ _ [10,144,33,288,65] 13 (by decide) (choices 1) [2,4,64] r33570 c33570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16682
  · exact u16683
  · exact u16684

def b33571 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 11 146 37 296 82 101 69 197 325), lower := (rows 11 146 37 296 82 32 64 128 256), losses := [] }

theorem u33571 : Upper (D 6) (R 6) [10,144,33,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33572 : Route 9 := (fun mask => (mask,id))

def c33572 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33572 : Upper (D 6) (R 6) [10,144,33,288,68] 13 := by
  apply FastRouting.sound _ _ [10,144,33,288,68] 13 (by decide) (choices 1) [1,2,4,64] r33572 c33572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16685
  · exact u16686
  · exact u16687
  · exact u16688

def b33573 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 146 37 328 19 100 100 228 356), lower := (rows 11 146 37 328 19 32 64 128 256), losses := [] }

theorem u33573 : Upper (D 6) (R 6) [10,144,33,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33574 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 146 37 328 21 102 102 230 358), lower := (rows 11 146 37 328 21 32 64 128 256), losses := [] }

theorem u33574 : Upper (D 6) (R 6) [10,144,33,320,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33575 : Route 9 := (fun mask => (mask,id))

def c33575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33575 : Upper (D 6) (R 6) [10,144,33,320,6] 13 := by
  apply FastRouting.sound _ _ [10,144,33,320,6] 13 (by decide) (choices 1) [1,4,64] r33575 c33575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16689
  · exact u16690
  · exact u16691

def b33576 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 11 146 37 328 49 102 70 198 326), lower := (rows 11 146 37 328 49 32 64 128 256), losses := [] }

theorem u33576 : Upper (D 6) (R 6) [10,144,33,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33577 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 2, region := 328, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 11 146 37 328 50 101 69 197 325), lower := (rows 11 146 37 328 50 32 64 128 256), losses := [] }

theorem u33577 : Upper (D 6) (R 6) [10,144,33,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33578 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 37 328 52 103 71 199 327), lower := (rows 11 146 37 328 52 32 64 128 256), losses := [] }

theorem u33578 : Upper (D 6) (R 6) [10,144,33,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33579 : Route 9 := (fun mask => (mask,id))

def c33579 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33579 : Upper (D 6) (R 6) [10,144,33,320,65] 13 := by
  apply FastRouting.sound _ _ [10,144,33,320,65] 13 (by decide) (choices 1) [2,4] r33579 c33579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16692
  · exact u16693

def b33580 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 146 37 328 82 37 101 165 293), lower := (rows 11 146 37 328 82 32 64 128 256), losses := [] }

theorem u33580 : Upper (D 6) (R 6) [10,144,33,320,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33581 : Route 9 := (fun mask => (mask,id))

def c33581 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33581 : Upper (D 6) (R 6) [10,144,33,320,68] 13 := by
  apply FastRouting.sound _ _ [10,144,33,320,68] 13 (by decide) (choices 1) [1,2,4] r33581 c33581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16694
  · exact u16695
  · exact u16696

def r33582 : Route 9 := (fun mask => (mask,id))

def c33582 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33582 : Upper (D 6) (R 6) [10,144,33,320,96] 13 := by
  apply FastRouting.sound _ _ [10,144,33,320,96] 13 (by decide) (choices 1) [1,2,4] r33582 c33582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16697
  · exact u16698
  · exact u16699

def b33583 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 146 38 73 21 356 356 484 356), lower := (rows 11 146 38 73 21 32 64 128 256), losses := [] }

theorem u33583 : Upper (D 6) (R 6) [10,144,34,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33584 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 329, targets := 32 },{ cop := 4, region := 454, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 146 38 73 49 356 324 452 324), lower := (rows 11 146 38 73 49 32 64 128 256), losses := [] }

theorem u33584 : Upper (D 6) (R 6) [10,144,34,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33585 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 38 73 52 357 325 453 325), lower := (rows 11 146 38 73 52 32 64 128 256), losses := [] }

theorem u33585 : Upper (D 6) (R 6) [10,144,34,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33586 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 146 38 73 81 292 356 420 292), lower := (rows 11 146 38 73 81 32 64 128 256), losses := [] }

theorem u33586 : Upper (D 6) (R 6) [10,144,34,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33587 : Route 9 := (fun mask => (mask,id))

def c33587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33587 : Upper (D 6) (R 6) [10,144,34,65,68] 13 := by
  apply FastRouting.sound _ _ [10,144,34,65,68] 13 (by decide) (choices 1) [1,4,256] r33587 c33587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16700
  · exact u16701
  · exact u16702

def b33588 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 329, targets := 32 },{ cop := 0, region := 292, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 11 146 38 73 112 293 325 389 261), lower := (rows 11 146 38 73 112 32 64 128 256), losses := [] }

theorem u33588 : Upper (D 6) (R 6) [10,144,34,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33589 : Route 9 := (fun mask => (mask,id))

def c33589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33589 : Upper (D 6) (R 6) [10,144,34,65,257] 13 := by
  apply FastRouting.sound _ _ [10,144,34,65,257] 13 (by decide) (choices 1) [4,64] r33589 c33589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16703
  · exact u16704

def r33590 : Route 9 := (fun mask => (mask,id))

def c33590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33590 : Upper (D 6) (R 6) [10,144,34,65,260] 13 := by
  apply FastRouting.sound _ _ [10,144,34,65,260] 13 (by decide) (choices 1) [1,4,64] r33590 c33590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16705
  · exact u16706
  · exact u16707

def r33591 : Route 9 := (fun mask => (mask,id))

def c33591 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33591 : Upper (D 6) (R 6) [10,144,34,65,288] 13 := by
  apply FastRouting.sound _ _ [10,144,34,65,288] 13 (by decide) (choices 1) [1,4,64] r33591 c33591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16708
  · exact u16709
  · exact u16710

def r33592 : Route 9 := (fun mask => (mask,id))

def c33592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33592 : Upper (D 6) (R 6) [10,144,34,65,320] 13 := by
  apply FastRouting.sound _ _ [10,144,34,65,320] 13 (by decide) (choices 1) [1,4] r33592 c33592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16711
  · exact u16712

def r33593 : Route 9 := (fun mask => (mask,id))

def c33593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33593 : Upper (D 6) (R 6) [10,144,34,68,5] 13 := by
  apply FastRouting.sound _ _ [10,144,34,68,5] 13 (by decide) (choices 1) [1,64,256] r33593 c33593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16713
  · exact u16714
  · exact u16715

def r33594 : Route 9 := (fun mask => (mask,id))

def c33594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33594 : Upper (D 6) (R 6) [10,144,34,68,33] 13 := by
  apply FastRouting.sound _ _ [10,144,34,68,33] 13 (by decide) (choices 1) [1,4,64,256] r33594 c33594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16716
  · exact u16717
  · exact u16718
  · exact u16719

def b33595 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 146 38 76 52 353 321 449 321), lower := (rows 11 146 38 76 52 32 64 128 256), losses := [] }

theorem u33595 : Upper (D 6) (R 6) [10,144,34,68,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33596 : Route 9 := (fun mask => (mask,id))

def c33596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33596 : Upper (D 6) (R 6) [10,144,34,68,65] 13 := by
  apply FastRouting.sound _ _ [10,144,34,68,65] 13 (by decide) (choices 1) [1,4,256] r33596 c33596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16720
  · exact u16721
  · exact u16722

def b33597 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 146 38 76 84 289 353 417 289), lower := (rows 11 146 38 76 84 32 64 128 256), losses := [] }

theorem u33597 : Upper (D 6) (R 6) [10,144,34,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33598 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 329, targets := 32 },{ cop := 0, region := 292, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 11 146 38 76 112 293 325 389 261), lower := (rows 11 146 38 76 112 32 64 128 256), losses := [] }

theorem u33598 : Upper (D 6) (R 6) [10,144,34,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33599 : Route 9 := (fun mask => (mask,id))

def c33599 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33599 : Upper (D 6) (R 6) [10,144,34,68,257] 13 := by
  apply FastRouting.sound _ _ [10,144,34,68,257] 13 (by decide) (choices 1) [1,4,64] r33599 c33599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16723
  · exact u16724
  · exact u16725

#print axioms u33599
end Delivery.IrregularNine14.P06
