import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0304

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b34620 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 25 35 69 104 400 38 70 134 262), lower := (rows 25 35 69 104 400 32 64 128 256), losses := [] }

theorem u34620 : Upper (D 6) (R 6) [24,33,65,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34621 : Route 9 := (fun mask => (mask,id))

def c34621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34621 : Upper (D 6) (R 6) [24,33,65,130,258] 13 := by
  apply FastRouting.sound _ _ [24,33,65,130,258] 13 (by decide) (choices 1) [4,64] r34621 c34621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18272
  · exact u18273

def r34622 : Route 9 := (fun mask => (mask,id))

def c34622 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34622 : Upper (D 6) (R 6) [24,33,65,130,260] 13 := by
  apply FastRouting.sound _ _ [24,33,65,130,260] 13 (by decide) (choices 1) [2,4,64] r34622 c34622
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18274
  · exact u18275
  · exact u18276

def r34623 : Route 9 := (fun mask => (mask,id))

def c34623 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34623 : Upper (D 6) (R 6) [24,33,65,130,288] 13 := by
  apply FastRouting.sound _ _ [24,33,65,130,288] 13 (by decide) (choices 1) [2,4,64] r34623 c34623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18277
  · exact u18278
  · exact u18279

def r34624 : Route 9 := (fun mask => (mask,id))

def c34624 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34624 : Upper (D 6) (R 6) [24,33,65,130,320] 13 := by
  apply FastRouting.sound _ _ [24,33,65,130,320] 13 (by decide) (choices 1) [2,4] r34624 c34624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18280
  · exact u18281

def b34625 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 340, targets := 32 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 25 35 69 168 336 38 70 134 262), lower := (rows 25 35 69 168 336 32 64 128 256), losses := [] }

theorem u34625 : Upper (D 6) (R 6) [24,33,65,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34626 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 25 35 70 11 52 484 452 452 452), lower := (rows 25 35 70 11 52 32 64 128 256), losses := [] }

theorem u34626 : Upper (D 6) (R 6) [24,33,66,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34627 : PairBound 9 := { available := 388, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 25 35 70 11 112 420 452 388 388), lower := (rows 25 35 70 11 112 32 64 128 256), losses := [] }

theorem u34627 : Upper (D 6) (R 6) [24,33,66,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34628 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 70 11 148 356 356 484 356), lower := (rows 25 35 70 11 148 32 64 128 256), losses := [] }

theorem u34628 : Upper (D 6) (R 6) [24,33,66,3,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34629 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 25 35 70 11 176 356 324 452 324), lower := (rows 25 35 70 11 176 32 64 128 256), losses := [] }

theorem u34629 : Upper (D 6) (R 6) [24,33,66,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34630 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 70 11 208 292 356 420 292), lower := (rows 25 35 70 11 208 32 64 128 256), losses := [] }

theorem u34630 : Upper (D 6) (R 6) [24,33,66,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34631 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 35 70 11 400 100 100 228 356), lower := (rows 25 35 70 11 400 32 64 128 256), losses := [] }

theorem u34631 : Upper (D 6) (R 6) [24,33,66,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34632 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 35 70 13 22 480 480 480 480), lower := (rows 25 35 70 13 22 32 64 128 256), losses := [] }

theorem u34632 : Upper (D 6) (R 6) [24,33,66,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34633 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 25 35 70 13 50 484 452 452 452), lower := (rows 25 35 70 13 50 32 64 128 256), losses := [] }

theorem u34633 : Upper (D 6) (R 6) [24,33,66,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34634 : PairBound 9 := { available := 450, camps := [{ cop := 4, region := 9, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 70 13 52 482 450 450 450), lower := (rows 25 35 70 13 52 32 64 128 256), losses := [] }

theorem u34634 : Upper (D 6) (R 6) [24,33,66,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34635 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 25, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 35 70 13 82 420 484 420 420), lower := (rows 25 35 70 13 82 32 64 128 256), losses := [] }

theorem u34635 : Upper (D 6) (R 6) [24,33,66,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34636 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 25, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 70 13 84 418 482 418 418), lower := (rows 25 35 70 13 84 32 64 128 256), losses := [] }

theorem u34636 : Upper (D 6) (R 6) [24,33,66,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34637 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 35 70 13 112 422 454 390 390), lower := (rows 25 35 70 13 112 32 64 128 256), losses := [] }

theorem u34637 : Upper (D 6) (R 6) [24,33,66,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34638 : Route 9 := (fun mask => (mask,id))

def c34638 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34638 : Upper (D 6) (R 6) [24,33,66,5,130] 13 := by
  apply FastRouting.sound _ _ [24,33,66,5,130] 13 (by decide) (choices 1) [4,64,256] r34638 c34638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18282
  · exact u18283
  · exact u18284

def b34639 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 35 70 13 148 354 354 482 354), lower := (rows 25 35 70 13 148 32 64 128 256), losses := [] }

theorem u34639 : Upper (D 6) (R 6) [24,33,66,5,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34640 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 324, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 35 70 13 176 358 326 454 326), lower := (rows 25 35 70 13 176 32 64 128 256), losses := [] }

theorem u34640 : Upper (D 6) (R 6) [24,33,66,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34641 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 290, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 25 35 70 13 208 294 358 422 294), lower := (rows 25 35 70 13 208 32 64 128 256), losses := [] }

theorem u34641 : Upper (D 6) (R 6) [24,33,66,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r34642 : Route 9 := (fun mask => (mask,id))

def c34642 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34642 : Upper (D 6) (R 6) [24,33,66,5,384] 13 := by
  apply FastRouting.sound _ _ [24,33,66,5,384] 13 (by decide) (choices 1) [2,4,64] r34642 c34642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18285
  · exact u18286
  · exact u18287

def b34643 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 70 14 52 481 449 449 449), lower := (rows 25 35 70 14 52 32 64 128 256), losses := [] }

theorem u34643 : Upper (D 6) (R 6) [24,33,66,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34644 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 70 14 112 421 453 389 389), lower := (rows 25 35 70 14 112 32 64 128 256), losses := [] }

theorem u34644 : Upper (D 6) (R 6) [24,33,66,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34645 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 332, targets := 1 },{ cop := 2, region := 8, targets := 32 }], pairs := [(2,0),(3,0),(3,5)], upper := (rows 25 35 70 14 145 356 356 484 356), lower := (rows 25 35 70 14 145 32 64 128 256), losses := [] }

theorem u34645 : Upper (D 6) (R 6) [24,33,66,6,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34646 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 70 14 148 353 353 481 353), lower := (rows 25 35 70 14 148 32 64 128 256), losses := [] }

theorem u34646 : Upper (D 6) (R 6) [24,33,66,6,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34647 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 70 14 176 357 325 453 325), lower := (rows 25 35 70 14 176 32 64 128 256), losses := [] }

theorem u34647 : Upper (D 6) (R 6) [24,33,66,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34648 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 70 14 208 293 357 421 293), lower := (rows 25 35 70 14 208 32 64 128 256), losses := [] }

theorem u34648 : Upper (D 6) (R 6) [24,33,66,6,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34649 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 35 70 14 400 101 101 229 357), lower := (rows 25 35 70 14 400 32 64 128 256), losses := [] }

theorem u34649 : Upper (D 6) (R 6) [24,33,66,6,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34649 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34650 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 70 41 146 356 324 452 324), lower := (rows 25 35 70 41 146 32 64 128 256), losses := [] }

theorem u34650 : Upper (D 6) (R 6) [24,33,66,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34651 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 70 41 148 358 326 454 326), lower := (rows 25 35 70 41 148 32 64 128 256), losses := [] }

theorem u34651 : Upper (D 6) (R 6) [24,33,66,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34652 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 70 41 208 294 326 390 262), lower := (rows 25 35 70 41 208 32 64 128 256), losses := [] }

theorem u34652 : Upper (D 6) (R 6) [24,33,66,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34652 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34653 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 8, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 70 41 400 102 70 198 326), lower := (rows 25 35 70 41 400 32 64 128 256), losses := [] }

theorem u34653 : Upper (D 6) (R 6) [24,33,66,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34654 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 469, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 70 42 145 356 324 452 324), lower := (rows 25 35 70 42 145 32 64 128 256), losses := [] }

theorem u34654 : Upper (D 6) (R 6) [24,33,66,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34655 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 70 42 148 357 325 453 325), lower := (rows 25 35 70 42 148 32 64 128 256), losses := [] }

theorem u34655 : Upper (D 6) (R 6) [24,33,66,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34656 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 70 42 208 293 325 389 261), lower := (rows 25 35 70 42 208 32 64 128 256), losses := [] }

theorem u34656 : Upper (D 6) (R 6) [24,33,66,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34657 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 35 70 42 400 101 69 197 325), lower := (rows 25 35 70 42 400 32 64 128 256), losses := [] }

theorem u34657 : Upper (D 6) (R 6) [24,33,66,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34658 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 25 35 70 44 81 422 454 390 390), lower := (rows 25 35 70 44 81 32 64 128 256), losses := [] }

theorem u34658 : Upper (D 6) (R 6) [24,33,66,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34659 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 16, targets := 1 }], pairs := [(2,5),(4,0),(4,5)], upper := (rows 25 35 70 44 82 421 453 389 389), lower := (rows 25 35 70 44 82 32 64 128 256), losses := [] }

theorem u34659 : Upper (D 6) (R 6) [24,33,66,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34660 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 35 70 44 84 419 451 387 387), lower := (rows 25 35 70 44 84 32 64 128 256), losses := [] }

theorem u34660 : Upper (D 6) (R 6) [24,33,66,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34660 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34661 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 332, targets := 1 },{ cop := 1, region := 324, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 25 35 70 44 145 358 326 454 326), lower := (rows 25 35 70 44 145 32 64 128 256), losses := [] }

theorem u34661 : Upper (D 6) (R 6) [24,33,66,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34661 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34662 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 468, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 70 44 146 357 325 453 325), lower := (rows 25 35 70 44 146 32 64 128 256), losses := [{ target := 5, region := (rows 9 2 22 8 22 0 75 139 267), good := (rows 477 471 470 477 470 0 64 128 256) }] }

theorem u34662 : Upper (D 6) (R 6) [24,33,66,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34662 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34663 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 0, region := 354, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 25 35 70 44 148 355 323 451 323), lower := (rows 25 35 70 44 148 32 64 128 256), losses := [] }

theorem u34663 : Upper (D 6) (R 6) [24,33,66,36,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34663 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34664 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 468, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 70 44 208 295 327 391 263), lower := (rows 25 35 70 44 208 32 64 128 256), losses := [{ target := 5, region := (rows 9 2 6 8 22 0 66 130 258), good := (rows 25 471 470 29 208 0 64 128 256) }] }

theorem u34664 : Upper (D 6) (R 6) [24,33,66,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34664 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34665 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 468, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 70 44 400 103 71 199 327), lower := (rows 25 35 70 44 400 32 64 128 256), losses := [{ target := 5, region := (rows 9 2 6 8 22 0 66 130 258), good := (rows 25 471 470 29 400 0 64 128 256) }] }

theorem u34665 : Upper (D 6) (R 6) [24,33,66,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34665 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34666 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 2, region := 432, targets := 64 }], pairs := [(2,0),(4,0),(4,6)], upper := (rows 25 35 70 73 146 292 356 420 292), lower := (rows 25 35 70 73 146 32 64 128 256), losses := [] }

theorem u34666 : Upper (D 6) (R 6) [24,33,66,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34666 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34667 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 2, region := 432, targets := 64 }], pairs := [(2,0),(4,0),(4,6)], upper := (rows 25 35 70 73 148 294 358 422 294), lower := (rows 25 35 70 73 148 32 64 128 256), losses := [] }

theorem u34667 : Upper (D 6) (R 6) [24,33,66,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34667 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34668 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 1, region := 324, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 35 70 73 176 294 326 390 262), lower := (rows 25 35 70 73 176 32 64 128 256), losses := [] }

theorem u34668 : Upper (D 6) (R 6) [24,33,66,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34668 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34669 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 2, region := 432, targets := 64 }], pairs := [(2,0),(4,0),(4,6)], upper := (rows 25 35 70 73 400 38 102 166 294), lower := (rows 25 35 70 73 400 32 64 128 256), losses := [] }

theorem u34669 : Upper (D 6) (R 6) [24,33,66,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34669 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34670 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 332, targets := 1 },{ cop := 2, region := 8, targets := 4 }], pairs := [(2,0),(3,0),(3,2)], upper := (rows 25 35 70 74 145 292 356 420 292), lower := (rows 25 35 70 74 145 32 64 128 256), losses := [] }

theorem u34670 : Upper (D 6) (R 6) [24,33,66,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34670 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34671 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 8, targets := 33 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5)], upper := (rows 25 35 70 74 148 293 357 421 293), lower := (rows 25 35 70 74 148 32 64 128 256), losses := [] }

theorem u34671 : Upper (D 6) (R 6) [24,33,66,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34671 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34672 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 332, targets := 32 },{ cop := 2, region := 8, targets := 1 }], pairs := [(2,5),(3,0),(3,5)], upper := (rows 25 35 70 74 176 293 325 389 261), lower := (rows 25 35 70 74 176 32 64 128 256), losses := [] }

theorem u34672 : Upper (D 6) (R 6) [24,33,66,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34672 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34673 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 8, targets := 33 },{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0),(3,0),(3,5)], upper := (rows 25 35 70 74 400 37 101 165 293), lower := (rows 25 35 70 74 400 32 64 128 256), losses := [] }

theorem u34673 : Upper (D 6) (R 6) [24,33,66,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34673 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34674 : PairBound 9 := { available := 294, camps := [{ cop := 3, region := 435, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 25 35 70 76 145 294 358 422 294), lower := (rows 25 35 70 76 145 32 64 128 256), losses := [] }

theorem u34674 : Upper (D 6) (R 6) [24,33,66,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34674 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34675 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 70 76 146 293 357 421 293), lower := (rows 25 35 70 76 146 32 64 128 256), losses := [] }

theorem u34675 : Upper (D 6) (R 6) [24,33,66,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34675 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34676 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 70 76 148 291 355 419 291), lower := (rows 25 35 70 76 148 32 64 128 256), losses := [] }

theorem u34676 : Upper (D 6) (R 6) [24,33,66,68,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34676 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34677 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 70 76 176 295 327 391 263), lower := (rows 25 35 70 76 176 32 64 128 256), losses := [] }

theorem u34677 : Upper (D 6) (R 6) [24,33,66,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34677 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34678 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 35 70 76 400 39 103 167 295), lower := (rows 25 35 70 76 400 32 64 128 256), losses := [] }

theorem u34678 : Upper (D 6) (R 6) [24,33,66,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34678 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b34679 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 332, targets := 1 },{ cop := 1, region := 324, targets := 32 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 25 35 70 104 145 294 326 390 262), lower := (rows 25 35 70 104 145 32 64 128 256), losses := [] }

theorem u34679 : Upper (D 6) (R 6) [24,33,66,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b34679 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u34679
end Delivery.IrregularNine14.P06
