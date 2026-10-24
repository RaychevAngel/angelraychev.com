import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0090

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18600 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 388 14 82 33 100 228 356), lower := (rows 25 35 388 14 82 33 64 128 256), losses := [] }

theorem u18600 : Upper (D 6) (R 6) [24,33,384,6,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18601 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 1, region := 80, targets := 4 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 25 35 388 14 82 36 97 225 353), lower := (rows 25 35 388 14 82 36 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 26 32 66 130 258), good := (rows 25 499 384 475 466 32 64 128 256) }] }

theorem u18601 : Upper (D 6) (R 6) [24,33,384,6,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18602 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 396, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(2,6),(3,6)], upper := (rows 25 35 388 14 82 96 101 165 293), lower := (rows 25 35 388 14 82 96 64 128 256), losses := [] }

theorem u18602 : Upper (D 6) (R 6) [24,33,384,6,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18603 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 388 14 84 33 98 226 354), lower := (rows 25 35 388 14 84 33 64 128 256), losses := [] }

theorem u18603 : Upper (D 6) (R 6) [24,33,384,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18604 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 388 14 84 34 97 225 353), lower := (rows 25 35 388 14 84 34 64 128 256), losses := [] }

theorem u18604 : Upper (D 6) (R 6) [24,33,384,6,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18605 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 396, targets := 64 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,6),(3,6)], upper := (rows 25 35 388 14 84 96 99 163 291), lower := (rows 25 35 388 14 84 96 64 128 256), losses := [] }

theorem u18605 : Upper (D 6) (R 6) [24,33,384,6,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18606 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 388 14 112 33 70 198 326), lower := (rows 25 35 388 14 112 33 64 128 256), losses := [] }

theorem u18606 : Upper (D 6) (R 6) [24,33,384,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18607 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 388 14 112 34 69 197 325), lower := (rows 25 35 388 14 112 34 64 128 256), losses := [] }

theorem u18607 : Upper (D 6) (R 6) [24,33,384,6,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18608 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 460, targets := 32 },{ cop := 1, region := 80, targets := 4 }], pairs := [(2,5),(3,5),(4,2)], upper := (rows 25 35 388 14 112 36 67 195 323), lower := (rows 25 35 388 14 112 36 64 128 256), losses := [] }

theorem u18608 : Upper (D 6) (R 6) [24,33,384,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18609 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 35 388 14 112 96 71 135 263), lower := (rows 25 35 388 14 112 96 64 128 256), losses := [] }

theorem u18609 : Upper (D 6) (R 6) [24,33,384,6,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18610 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 388 44 82 33 70 198 326), lower := (rows 25 35 388 44 82 33 64 128 256), losses := [] }

theorem u18610 : Upper (D 6) (R 6) [24,33,384,36,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18611 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 388 44 82 34 69 197 325), lower := (rows 25 35 388 44 82 34 64 128 256), losses := [] }

theorem u18611 : Upper (D 6) (R 6) [24,33,384,36,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18612 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 25 35 388 44 82 36 67 195 323), lower := (rows 25 35 388 44 82 36 64 128 256), losses := [] }

theorem u18612 : Upper (D 6) (R 6) [24,33,384,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18613 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 388, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 25 35 388 44 82 96 71 135 263), lower := (rows 25 35 388 44 82 96 64 128 256), losses := [] }

theorem u18613 : Upper (D 6) (R 6) [24,33,384,36,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18614 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 388 74 84 33 102 166 294), lower := (rows 25 35 388 74 84 33 64 128 256), losses := [] }

theorem u18614 : Upper (D 6) (R 6) [24,33,384,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18615 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 35 388 74 84 34 101 165 293), lower := (rows 25 35 388 74 84 34 64 128 256), losses := [] }

theorem u18615 : Upper (D 6) (R 6) [24,33,384,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18616 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 1, region := 72, targets := 4 }], pairs := [(1,6),(2,6),(3,2)], upper := (rows 25 35 388 74 84 36 99 163 291), lower := (rows 25 35 388 74 84 36 64 128 256), losses := [] }

theorem u18616 : Upper (D 6) (R 6) [24,33,384,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18617 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 38 70 11 148 33 352 480 352), lower := (rows 25 38 70 11 148 33 64 128 256), losses := [] }

theorem u18617 : Upper (D 6) (R 6) [24,36,66,3,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18618 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 70 11 148 96 353 417 289), lower := (rows 25 38 70 11 148 96 64 128 256), losses := [] }

theorem u18618 : Upper (D 6) (R 6) [24,36,66,3,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18619 : Route 9 := (fun mask => (mask,id))

def c18619 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18619 : Upper (D 6) (R 6) [24,36,66,3,132,256] 13 := by
  apply FastRouting.sound _ _ [24,36,66,3,132,256] 13 (by decide) (choices 1) [1,32] r18619 c18619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5417
  · exact u5418

def b18620 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 70 11 176 33 324 452 324), lower := (rows 25 38 70 11 176 33 64 128 256), losses := [] }

theorem u18620 : Upper (D 6) (R 6) [24,36,66,3,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18620 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18621 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 11 176 36 321 449 321), lower := (rows 25 38 70 11 176 36 64 128 256), losses := [] }

theorem u18621 : Upper (D 6) (R 6) [24,36,66,3,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18622 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 70 11 176 96 325 389 261), lower := (rows 25 38 70 11 176 96 64 128 256), losses := [] }

theorem u18622 : Upper (D 6) (R 6) [24,36,66,3,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18623 : Route 9 := (fun mask => (mask,id))

def c18623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18623 : Upper (D 6) (R 6) [24,36,66,3,160,256] 13 := by
  apply FastRouting.sound _ _ [24,36,66,3,160,256] 13 (by decide) (choices 1) [1,4] r18623 c18623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5419
  · exact u5420

def b18624 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 70 11 208 33 356 420 292), lower := (rows 25 38 70 11 208 33 64 128 256), losses := [] }

theorem u18624 : Upper (D 6) (R 6) [24,36,66,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18625 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 11 208 36 353 417 289), lower := (rows 25 38 70 11 208 36 64 128 256), losses := [] }

theorem u18625 : Upper (D 6) (R 6) [24,36,66,3,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18626 : Route 9 := (fun mask => (mask,id))

def c18626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18626 : Upper (D 6) (R 6) [24,36,66,3,192,256] 13 := by
  apply FastRouting.sound _ _ [24,36,66,3,192,256] 13 (by decide) (choices 1) [1,4,32] r18626 c18626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5421
  · exact u5422
  · exact u5423

def b18627 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 70 11 400 33 100 228 356), lower := (rows 25 38 70 11 400 33 64 128 256), losses := [] }

theorem u18627 : Upper (D 6) (R 6) [24,36,66,3,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18628 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 11 400 36 97 225 353), lower := (rows 25 38 70 11 400 36 64 128 256), losses := [] }

theorem u18628 : Upper (D 6) (R 6) [24,36,66,3,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18629 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 70 11 400 96 101 165 293), lower := (rows 25 38 70 11 400 96 64 128 256), losses := [] }

theorem u18629 : Upper (D 6) (R 6) [24,36,66,3,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18630 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 38 70 41 146 33 324 452 324), lower := (rows 25 38 70 41 146 33 64 128 256), losses := [] }

theorem u18630 : Upper (D 6) (R 6) [24,36,66,33,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18631 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 41 146 36 321 449 321), lower := (rows 25 38 70 41 146 36 64 128 256), losses := [] }

theorem u18631 : Upper (D 6) (R 6) [24,36,66,33,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18632 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 70 41 146 96 325 389 261), lower := (rows 25 38 70 41 146 96 64 128 256), losses := [] }

theorem u18632 : Upper (D 6) (R 6) [24,36,66,33,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18633 : Route 9 := (fun mask => (mask,id))

def c18633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18633 : Upper (D 6) (R 6) [24,36,66,33,130,256] 13 := by
  apply FastRouting.sound _ _ [24,36,66,33,130,256] 13 (by decide) (choices 1) [1,4] r18633 c18633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5424
  · exact u5425

def b18634 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 38 70 41 148 33 322 450 322), lower := (rows 25 38 70 41 148 33 64 128 256), losses := [] }

theorem u18634 : Upper (D 6) (R 6) [24,36,66,33,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18635 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 473, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 70 41 148 34 321 449 321), lower := (rows 25 38 70 41 148 34 64 128 256), losses := [] }

theorem u18635 : Upper (D 6) (R 6) [24,36,66,33,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18635 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18636 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 70 41 148 96 323 387 259), lower := (rows 25 38 70 41 148 96 64 128 256), losses := [] }

theorem u18636 : Upper (D 6) (R 6) [24,36,66,33,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18637 : Route 9 := (fun mask => (mask,id))

def c18637 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18637 : Upper (D 6) (R 6) [24,36,66,33,132,256] 13 := by
  apply FastRouting.sound _ _ [24,36,66,33,132,256] 13 (by decide) (choices 1) [1,2] r18637 c18637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5426
  · exact u5427

def b18638 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 38 70 41 208 33 326 390 262), lower := (rows 25 38 70 41 208 33 64 128 256), losses := [] }

theorem u18638 : Upper (D 6) (R 6) [24,36,66,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18639 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 473, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 70 41 208 34 325 389 261), lower := (rows 25 38 70 41 208 34 64 128 256), losses := [] }

theorem u18639 : Upper (D 6) (R 6) [24,36,66,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18640 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 41 208 36 323 387 259), lower := (rows 25 38 70 41 208 36 64 128 256), losses := [] }

theorem u18640 : Upper (D 6) (R 6) [24,36,66,33,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18640 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18641 : Route 9 := (fun mask => (mask,id))

def c18641 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18641 : Upper (D 6) (R 6) [24,36,66,33,192,256] 13 := by
  apply FastRouting.sound _ _ [24,36,66,33,192,256] 13 (by decide) (choices 1) [1,2,4] r18641 c18641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5428
  · exact u5429
  · exact u5430

def b18642 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 38 70 41 400 33 70 198 326), lower := (rows 25 38 70 41 400 33 64 128 256), losses := [] }

theorem u18642 : Upper (D 6) (R 6) [24,36,66,33,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18642 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18643 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 473, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 70 41 400 34 69 197 325), lower := (rows 25 38 70 41 400 34 64 128 256), losses := [] }

theorem u18643 : Upper (D 6) (R 6) [24,36,66,33,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18643 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18644 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 41 400 36 67 195 323), lower := (rows 25 38 70 41 400 36 64 128 256), losses := [] }

theorem u18644 : Upper (D 6) (R 6) [24,36,66,33,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18644 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18645 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 70 41 400 96 71 135 263), lower := (rows 25 38 70 41 400 96 64 128 256), losses := [] }

theorem u18645 : Upper (D 6) (R 6) [24,36,66,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18645 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18646 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 334, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 38 70 104 145 33 326 390 262), lower := (rows 25 38 70 104 145 33 64 128 256), losses := [] }

theorem u18646 : Upper (D 6) (R 6) [24,36,66,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18646 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18647 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 473, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 70 104 145 34 325 389 261), lower := (rows 25 38 70 104 145 34 64 128 256), losses := [] }

theorem u18647 : Upper (D 6) (R 6) [24,36,66,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18647 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18648 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 104 145 36 323 387 259), lower := (rows 25 38 70 104 145 36 64 128 256), losses := [] }

theorem u18648 : Upper (D 6) (R 6) [24,36,66,96,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18648 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18649 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 38 70 104 145 288 71 135 263), lower := (rows 25 38 70 104 145 288 64 128 256), losses := [] }

theorem u18649 : Upper (D 6) (R 6) [24,36,66,96,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18649 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18650 : Route 9 := (fun mask => (mask,id))

def c18650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u18650 : Upper (D 6) (R 6) [24,36,66,96,130,1] 13 := by
  apply FastRouting.sound _ _ [24,36,66,96,130,1] 13 (by decide) (choices 1) [1,4,256] r18650 c18650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5431
  · exact u5432
  · exact u5433

def b18651 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 104 146 36 321 385 257), lower := (rows 25 38 70 104 146 36 64 128 256), losses := [] }

theorem u18651 : Upper (D 6) (R 6) [24,36,66,96,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18651 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18652 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 38 70 104 146 288 69 133 261), lower := (rows 25 38 70 104 146 288 64 128 256), losses := [] }

theorem u18652 : Upper (D 6) (R 6) [24,36,66,96,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18652 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18653 : Route 9 := (fun mask => (mask,id))

def c18653 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18653 : Upper (D 6) (R 6) [24,36,66,96,384,1] 13 := by
  apply FastRouting.sound _ _ [24,36,66,96,384,1] 13 (by decide) (choices 1) [1,2,4] r18653 c18653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5434
  · exact u5435
  · exact u5436

def b18654 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 473, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 70 104 400 34 69 133 261), lower := (rows 25 38 70 104 400 34 64 128 256), losses := [] }

theorem u18654 : Upper (D 6) (R 6) [24,36,66,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18654 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18655 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 104 400 36 67 131 259), lower := (rows 25 38 70 104 400 36 64 128 256), losses := [] }

theorem u18655 : Upper (D 6) (R 6) [24,36,66,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18655 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18656 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 473, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 70 137 273 34 100 228 356), lower := (rows 25 38 70 137 273 34 64 128 256), losses := [] }

theorem u18656 : Upper (D 6) (R 6) [24,36,66,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18656 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18657 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 473, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 70 137 273 36 98 226 354), lower := (rows 25 38 70 137 273 36 64 128 256), losses := [] }

theorem u18657 : Upper (D 6) (R 6) [24,36,66,129,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18657 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18658 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 70 137 273 96 102 166 294), lower := (rows 25 38 70 137 273 96 64 128 256), losses := [] }

theorem u18658 : Upper (D 6) (R 6) [24,36,66,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18658 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18659 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 70 137 274 33 100 228 356), lower := (rows 25 38 70 137 274 33 64 128 256), losses := [] }

theorem u18659 : Upper (D 6) (R 6) [24,36,66,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18659 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u18659
end Delivery.IrregularNine14.P06
