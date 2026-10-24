import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0041

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12600 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 148 13 304 36 66 194 322), lower := (rows 11 35 148 13 304 36 64 128 256), losses := [] }

theorem u12600 : Upper (D 6) (R 6) [10,33,144,5,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12601 : Route 9 := (fun mask => (mask,id))

def c12601 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12601 : Upper (D 6) (R 6) [10,33,144,5,288,64] 13 := by
  apply FastRouting.sound _ _ [10,33,144,5,288,64] 13 (by decide) (choices 1) [2,4] r12601 c12601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2474
  · exact u2475

def b12602 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 13 336 34 100 228 356), lower := (rows 11 35 148 13 336 34 64 128 256), losses := [] }

theorem u12602 : Upper (D 6) (R 6) [10,33,144,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12603 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 148 13 336 36 98 226 354), lower := (rows 11 35 148 13 336 36 64 128 256), losses := [] }

theorem u12603 : Upper (D 6) (R 6) [10,33,144,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12604 : Route 9 := (fun mask => (mask,id))

def c12604 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12604 : Upper (D 6) (R 6) [10,33,144,5,320,64] 13 := by
  apply FastRouting.sound _ _ [10,33,144,5,320,64] 13 (by decide) (choices 1) [2,4,32] r12604 c12604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2476
  · exact u2477
  · exact u2478

def b12605 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 73 52 34 324 452 324), lower := (rows 11 35 148 73 52 34 64 128 256), losses := [] }

theorem u12605 : Upper (D 6) (R 6) [10,33,144,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12606 : PairBound 9 := { available := 322, camps := [{ cop := 7, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 148 73 52 36 322 450 322), lower := (rows 11 35 148 73 52 36 64 128 256), losses := [] }

theorem u12606 : Upper (D 6) (R 6) [10,33,144,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12607 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 148 73 52 96 326 390 262), lower := (rows 11 35 148 73 52 96 64 128 256), losses := [] }

theorem u12607 : Upper (D 6) (R 6) [10,33,144,65,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12608 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 148 73 52 288 70 198 326), lower := (rows 11 35 148 73 52 288 64 128 256), losses := [] }

theorem u12608 : Upper (D 6) (R 6) [10,33,144,65,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12608 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12609 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 73 84 34 356 420 292), lower := (rows 11 35 148 73 84 34 64 128 256), losses := [] }

theorem u12609 : Upper (D 6) (R 6) [10,33,144,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12610 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 148 73 84 36 354 418 290), lower := (rows 11 35 148 73 84 36 64 128 256), losses := [] }

theorem u12610 : Upper (D 6) (R 6) [10,33,144,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12611 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 148 73 84 288 102 166 294), lower := (rows 11 35 148 73 84 288 64 128 256), losses := [] }

theorem u12611 : Upper (D 6) (R 6) [10,33,144,65,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12611 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12612 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 73 276 34 100 228 356), lower := (rows 11 35 148 73 276 34 64 128 256), losses := [] }

theorem u12612 : Upper (D 6) (R 6) [10,33,144,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12613 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 148 73 276 36 98 226 354), lower := (rows 11 35 148 73 276 36 64 128 256), losses := [] }

theorem u12613 : Upper (D 6) (R 6) [10,33,144,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12614 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 148 73 276 96 102 166 294), lower := (rows 11 35 148 73 276 96 64 128 256), losses := [] }

theorem u12614 : Upper (D 6) (R 6) [10,33,144,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12615 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 73 304 34 68 196 324), lower := (rows 11 35 148 73 304 34 64 128 256), losses := [] }

theorem u12615 : Upper (D 6) (R 6) [10,33,144,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12616 : Route 9 := (fun mask => (mask,id))

def c12616 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12616 : Upper (D 6) (R 6) [10,33,144,65,288,4] 13 := by
  apply FastRouting.sound _ _ [10,33,144,65,288,4] 13 (by decide) (choices 1) [2,4] r12616 c12616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2479
  · exact u2480

def b12617 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 148 73 304 96 70 134 262), lower := (rows 11 35 148 73 304 96 64 128 256), losses := [] }

theorem u12617 : Upper (D 6) (R 6) [10,33,144,65,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12618 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 73 336 34 100 164 292), lower := (rows 11 35 148 73 336 34 64 128 256), losses := [] }

theorem u12618 : Upper (D 6) (R 6) [10,33,144,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12619 : Route 9 := (fun mask => (mask,id))

def c12619 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12619 : Upper (D 6) (R 6) [10,33,144,65,320,4] 13 := by
  apply FastRouting.sound _ _ [10,33,144,65,320,4] 13 (by decide) (choices 1) [2,4,32] r12619 c12619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2481
  · exact u2482
  · exact u2483

def b12620 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 148 76 52 33 322 450 322), lower := (rows 11 35 148 76 52 33 64 128 256), losses := [] }

theorem u12620 : Upper (D 6) (R 6) [10,33,144,68,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12621 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 148 76 52 34 321 449 321), lower := (rows 11 35 148 76 52 34 64 128 256), losses := [] }

theorem u12621 : Upper (D 6) (R 6) [10,33,144,68,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12622 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 48, targets := 1 }], pairs := [(2,6),(4,0),(4,6)], upper := (rows 11 35 148 76 52 96 323 387 259), lower := (rows 11 35 148 76 52 96 64 128 256), losses := [] }

theorem u12622 : Upper (D 6) (R 6) [10,33,144,68,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12623 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 148 76 52 288 67 195 323), lower := (rows 11 35 148 76 52 288 64 128 256), losses := [] }

theorem u12623 : Upper (D 6) (R 6) [10,33,144,68,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12623 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12624 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 148 76 82 33 356 420 292), lower := (rows 11 35 148 76 82 33 64 128 256), losses := [] }

theorem u12624 : Upper (D 6) (R 6) [10,33,144,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12625 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 148 76 82 36 353 417 289), lower := (rows 11 35 148 76 82 36 64 128 256), losses := [] }

theorem u12625 : Upper (D 6) (R 6) [10,33,144,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12626 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 148 76 82 288 101 165 293), lower := (rows 11 35 148 76 82 288 64 128 256), losses := [] }

theorem u12626 : Upper (D 6) (R 6) [10,33,144,68,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12626 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12627 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 148 76 112 33 326 390 262), lower := (rows 11 35 148 76 112 33 64 128 256), losses := [] }

theorem u12627 : Upper (D 6) (R 6) [10,33,144,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12628 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 148 76 112 34 325 389 261), lower := (rows 11 35 148 76 112 34 64 128 256), losses := [] }

theorem u12628 : Upper (D 6) (R 6) [10,33,144,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12629 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 11 35 148 76 112 36 323 387 259), lower := (rows 11 35 148 76 112 36 64 128 256), losses := [] }

theorem u12629 : Upper (D 6) (R 6) [10,33,144,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12630 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 148 76 112 288 71 135 263), lower := (rows 11 35 148 76 112 288 64 128 256), losses := [] }

theorem u12630 : Upper (D 6) (R 6) [10,33,144,68,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12630 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12631 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 76 273 34 100 228 356), lower := (rows 11 35 148 76 273 34 64 128 256), losses := [] }

theorem u12631 : Upper (D 6) (R 6) [10,33,144,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12632 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 148 76 273 36 98 226 354), lower := (rows 11 35 148 76 273 36 64 128 256), losses := [] }

theorem u12632 : Upper (D 6) (R 6) [10,33,144,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12633 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 148 76 273 96 102 166 294), lower := (rows 11 35 148 76 273 96 64 128 256), losses := [] }

theorem u12633 : Upper (D 6) (R 6) [10,33,144,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12634 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 76 274 33 100 228 356), lower := (rows 11 35 148 76 274 33 64 128 256), losses := [] }

theorem u12634 : Upper (D 6) (R 6) [10,33,144,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12635 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 148 76 274 36 97 225 353), lower := (rows 11 35 148 76 274 36 64 128 256), losses := [] }

theorem u12635 : Upper (D 6) (R 6) [10,33,144,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12636 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 148 76 274 96 101 165 293), lower := (rows 11 35 148 76 274 96 64 128 256), losses := [] }

theorem u12636 : Upper (D 6) (R 6) [10,33,144,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12637 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 148 76 276 33 98 226 354), lower := (rows 11 35 148 76 276 33 64 128 256), losses := [] }

theorem u12637 : Upper (D 6) (R 6) [10,33,144,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12638 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 148 76 276 34 97 225 353), lower := (rows 11 35 148 76 276 34 64 128 256), losses := [] }

theorem u12638 : Upper (D 6) (R 6) [10,33,144,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12639 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 148 76 276 96 99 163 291), lower := (rows 11 35 148 76 276 96 64 128 256), losses := [] }

theorem u12639 : Upper (D 6) (R 6) [10,33,144,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12640 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 76 304 33 70 198 326), lower := (rows 11 35 148 76 304 33 64 128 256), losses := [] }

theorem u12640 : Upper (D 6) (R 6) [10,33,144,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12641 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 76 304 34 69 197 325), lower := (rows 11 35 148 76 304 34 64 128 256), losses := [] }

theorem u12641 : Upper (D 6) (R 6) [10,33,144,68,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12641 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12642 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 148 76 304 36 67 195 323), lower := (rows 11 35 148 76 304 36 64 128 256), losses := [] }

theorem u12642 : Upper (D 6) (R 6) [10,33,144,68,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12643 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 148 76 304 96 71 135 263), lower := (rows 11 35 148 76 304 96 64 128 256), losses := [] }

theorem u12643 : Upper (D 6) (R 6) [10,33,144,68,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12644 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 148 76 336 33 102 166 294), lower := (rows 11 35 148 76 336 33 64 128 256), losses := [] }

theorem u12644 : Upper (D 6) (R 6) [10,33,144,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12645 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 148 76 336 34 101 165 293), lower := (rows 11 35 148 76 336 34 64 128 256), losses := [] }

theorem u12645 : Upper (D 6) (R 6) [10,33,144,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12646 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 1, region := 336, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 35 148 76 336 36 99 163 291), lower := (rows 11 35 148 76 336 36 64 128 256), losses := [] }

theorem u12646 : Upper (D 6) (R 6) [10,33,144,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12647 : PairBound 9 := { available := 68, camps := [{ cop := 8, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 265 52 34 68 196 324), lower := (rows 11 35 148 265 52 34 64 128 256), losses := [] }

theorem u12647 : Upper (D 6) (R 6) [10,33,144,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12648 : PairBound 9 := { available := 66, camps := [{ cop := 7, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 148 265 52 36 66 194 322), lower := (rows 11 35 148 265 52 36 64 128 256), losses := [] }

theorem u12648 : Upper (D 6) (R 6) [10,33,144,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12649 : Route 9 := (fun mask => (mask,id))

def c12649 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12649 : Upper (D 6) (R 6) [10,33,144,257,36,64] 13 := by
  apply FastRouting.sound _ _ [10,33,144,257,36,64] 13 (by decide) (choices 1) [2,4] r12649 c12649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2484
  · exact u2485

def b12650 : PairBound 9 := { available := 100, camps := [{ cop := 8, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 265 84 34 100 228 356), lower := (rows 11 35 148 265 84 34 64 128 256), losses := [] }

theorem u12650 : Upper (D 6) (R 6) [10,33,144,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12650 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12651 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 148 265 84 36 98 226 354), lower := (rows 11 35 148 265 84 36 64 128 256), losses := [] }

theorem u12651 : Upper (D 6) (R 6) [10,33,144,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12652 : Route 9 := (fun mask => (mask,id))

def c12652 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12652 : Upper (D 6) (R 6) [10,33,144,257,68,64] 13 := by
  apply FastRouting.sound _ _ [10,33,144,257,68,64] 13 (by decide) (choices 1) [2,4,32] r12652 c12652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2486
  · exact u2487
  · exact u2488

def b12653 : PairBound 9 := { available := 68, camps := [{ cop := 8, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 265 112 34 68 196 324), lower := (rows 11 35 148 265 112 34 64 128 256), losses := [] }

theorem u12653 : Upper (D 6) (R 6) [10,33,144,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12653 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12654 : Route 9 := (fun mask => (mask,id))

def c12654 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12654 : Upper (D 6) (R 6) [10,33,144,257,96,4] 13 := by
  apply FastRouting.sound _ _ [10,33,144,257,96,4] 13 (by decide) (choices 1) [2,4] r12654 c12654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2489
  · exact u2490

def b12655 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 148 265 112 96 70 134 262), lower := (rows 11 35 148 265 112 96 64 128 256), losses := [] }

theorem u12655 : Upper (D 6) (R 6) [10,33,144,257,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12656 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 148 268 52 33 66 194 322), lower := (rows 11 35 148 268 52 33 64 128 256), losses := [] }

theorem u12656 : Upper (D 6) (R 6) [10,33,144,260,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b12657 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 148 268 52 34 65 193 321), lower := (rows 11 35 148 268 52 34 64 128 256), losses := [] }

theorem u12657 : Upper (D 6) (R 6) [10,33,144,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r12658 : Route 9 := (fun mask => (mask,id))

def c12658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12658 : Upper (D 6) (R 6) [10,33,144,260,36,64] 13 := by
  apply FastRouting.sound _ _ [10,33,144,260,36,64] 13 (by decide) (choices 1) [1,2] r12658 c12658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2491
  · exact u2492

def b12659 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 148 268 81 34 100 228 356), lower := (rows 11 35 148 268 81 34 64 128 256), losses := [] }

theorem u12659 : Upper (D 6) (R 6) [10,33,144,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b12659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u12659
end Delivery.IrregularNine14.P06
