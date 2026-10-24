import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0055

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14580 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 388 73 22 33 100 228 356), lower := (rows 11 50 388 73 22 33 64 128 256), losses := [] }

theorem u14580 : Upper (D 6) (R 6) [10,48,384,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14581 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 388 73 22 36 97 225 353), lower := (rows 11 50 388 73 22 36 64 128 256), losses := [] }

theorem u14581 : Upper (D 6) (R 6) [10,48,384,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14582 : Route 9 := (fun mask => (mask,id))

def c14582 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14582 : Upper (D 6) (R 6) [10,48,384,65,6,64] 13 := by
  apply FastRouting.sound _ _ [10,48,384,65,6,64] 13 (by decide) (choices 1) [1,4,32] r14582 c14582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3307
  · exact u3308
  · exact u3309

def b14583 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 388 73 84 33 102 166 294), lower := (rows 11 50 388 73 84 33 64 128 256), losses := [] }

theorem u14583 : Upper (D 6) (R 6) [10,48,384,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14584 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 388 73 84 34 101 165 293), lower := (rows 11 50 388 73 84 34 64 128 256), losses := [] }

theorem u14584 : Upper (D 6) (R 6) [10,48,384,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14585 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 388 73 84 36 99 163 291), lower := (rows 11 50 388 73 84 36 64 128 256), losses := [] }

theorem u14585 : Upper (D 6) (R 6) [10,48,384,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14586 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 388 76 21 33 98 226 354), lower := (rows 11 50 388 76 21 33 64 128 256), losses := [] }

theorem u14586 : Upper (D 6) (R 6) [10,48,384,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14587 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 388 76 21 34 97 225 353), lower := (rows 11 50 388 76 21 34 64 128 256), losses := [] }

theorem u14587 : Upper (D 6) (R 6) [10,48,384,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14588 : Route 9 := (fun mask => (mask,id))

def c14588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14588 : Upper (D 6) (R 6) [10,48,384,68,5,64] 13 := by
  apply FastRouting.sound _ _ [10,48,384,68,5,64] 13 (by decide) (choices 1) [1,2,32] r14588 c14588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3310
  · exact u3311
  · exact u3312

def b14589 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 388 76 22 33 97 225 353), lower := (rows 11 50 388 76 22 33 64 128 256), losses := [] }

theorem u14589 : Upper (D 6) (R 6) [10,48,384,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14590 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 3, region := 50, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 388 76 22 96 97 161 289), lower := (rows 11 50 388 76 22 96 64 128 256), losses := [] }

theorem u14590 : Upper (D 6) (R 6) [10,48,384,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14591 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 388 76 81 33 102 166 294), lower := (rows 11 50 388 76 81 33 64 128 256), losses := [] }

theorem u14591 : Upper (D 6) (R 6) [10,48,384,68,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14592 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 388 76 81 34 101 165 293), lower := (rows 11 50 388 76 81 34 64 128 256), losses := [] }

theorem u14592 : Upper (D 6) (R 6) [10,48,384,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14593 : Route 9 := (fun mask => (mask,id))

def c14593 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14593 : Upper (D 6) (R 6) [10,48,384,68,65,4] 13 := by
  apply FastRouting.sound _ _ [10,48,384,68,65,4] 13 (by decide) (choices 1) [1,2,32] r14593 c14593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3313
  · exact u3314
  · exact u3315

def b14594 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 452, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 388 104 21 33 70 198 326), lower := (rows 11 50 388 104 21 33 64 128 256), losses := [] }

theorem u14594 : Upper (D 6) (R 6) [10,48,384,96,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14595 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 388 104 21 34 69 197 325), lower := (rows 11 50 388 104 21 34 64 128 256), losses := [] }

theorem u14595 : Upper (D 6) (R 6) [10,48,384,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14596 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 388 104 21 36 67 195 323), lower := (rows 11 50 388 104 21 36 64 128 256), losses := [] }

theorem u14596 : Upper (D 6) (R 6) [10,48,384,96,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14597 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 50 388 104 21 96 71 135 263), lower := (rows 11 50 388 104 21 96 64 128 256), losses := [] }

theorem u14597 : Upper (D 6) (R 6) [10,48,384,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14598 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 98 22 44 145 33 324 452 324), lower := (rows 11 98 22 44 145 33 64 128 256), losses := [] }

theorem u14598 : Upper (D 6) (R 6) [10,96,18,36,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14599 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 98 22 44 145 36 321 449 321), lower := (rows 11 98 22 44 145 36 64 128 256), losses := [] }

theorem u14599 : Upper (D 6) (R 6) [10,96,18,36,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14600 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 22 44 145 96 325 389 261), lower := (rows 11 98 22 44 145 96 64 128 256), losses := [] }

theorem u14600 : Upper (D 6) (R 6) [10,96,18,36,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14601 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 98 22 44 145 288 69 197 325), lower := (rows 11 98 22 44 145 288 64 128 256), losses := [] }

theorem u14601 : Upper (D 6) (R 6) [10,96,18,36,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14601 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14602 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 98 22 44 400 33 69 197 325), lower := (rows 11 98 22 44 400 33 64 128 256), losses := [] }

theorem u14602 : Upper (D 6) (R 6) [10,96,18,36,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14603 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 98 22 44 400 36 65 193 321), lower := (rows 11 98 22 44 400 36 64 128 256), losses := [] }

theorem u14603 : Upper (D 6) (R 6) [10,96,18,36,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14604 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 22 44 400 96 69 133 261), lower := (rows 11 98 22 44 400 96 64 128 256), losses := [] }

theorem u14604 : Upper (D 6) (R 6) [10,96,18,36,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14605 : Route 9 := (fun mask => (mask,id))

def c14605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14605 : Upper (D 6) (R 6) [10,96,18,129,257,4] 13 := by
  apply FastRouting.sound _ _ [10,96,18,129,257,4] 13 (by decide) (choices 1) [4,32] r14605 c14605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3316
  · exact u3317

def b14606 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 22 137 273 96 100 164 292), lower := (rows 11 98 22 137 273 96 64 128 256), losses := [] }

theorem u14606 : Upper (D 6) (R 6) [10,96,18,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14607 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 22 137 276 33 100 228 356), lower := (rows 11 98 22 137 276 33 64 128 256), losses := [] }

theorem u14607 : Upper (D 6) (R 6) [10,96,18,129,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14608 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 22 137 276 96 101 165 293), lower := (rows 11 98 22 137 276 96 64 128 256), losses := [] }

theorem u14608 : Upper (D 6) (R 6) [10,96,18,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14609 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 342, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 22 137 304 33 68 196 324), lower := (rows 11 98 22 137 304 33 64 128 256), losses := [] }

theorem u14609 : Upper (D 6) (R 6) [10,96,18,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14610 : Route 9 := (fun mask => (mask,id))

def c14610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14610 : Upper (D 6) (R 6) [10,96,18,129,288,4] 13 := by
  apply FastRouting.sound _ _ [10,96,18,129,288,4] 13 (by decide) (choices 1) [1,4] r14610 c14610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3318
  · exact u3319

def b14611 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 22 137 304 96 69 133 261), lower := (rows 11 98 22 137 304 96 64 128 256), losses := [] }

theorem u14611 : Upper (D 6) (R 6) [10,96,18,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14612 : Route 9 := (fun mask => (mask,id))

def c14612 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14612 : Upper (D 6) (R 6) [10,96,18,132,257,1] 13 := by
  apply FastRouting.sound _ _ [10,96,18,132,257,1] 13 (by decide) (choices 1) [4,32] r14612 c14612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3320
  · exact u3321

def b14613 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 22 140 273 96 101 165 293), lower := (rows 11 98 22 140 273 96 64 128 256), losses := [] }

theorem u14613 : Upper (D 6) (R 6) [10,96,18,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14614 : Route 9 := (fun mask => (mask,id))

def c14614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14614 : Upper (D 6) (R 6) [10,96,18,132,288,1] 13 := by
  apply FastRouting.sound _ _ [10,96,18,132,288,1] 13 (by decide) (choices 1) [1,4] r14614 c14614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3322
  · exact u3323

def b14615 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 98 22 140 304 36 65 193 321), lower := (rows 11 98 22 140 304 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 65 129 257), good := (rows 505 96 52 172 304 36 64 128 256) }] }

theorem u14615 : Upper (D 6) (R 6) [10,96,18,132,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14616 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 22 140 304 96 69 133 261), lower := (rows 11 98 22 140 304 96 64 128 256), losses := [] }

theorem u14616 : Upper (D 6) (R 6) [10,96,18,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14617 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 25 148 34 324 452 324), lower := (rows 11 98 37 25 148 34 64 128 256), losses := [] }

theorem u14617 : Upper (D 6) (R 6) [10,96,33,17,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14618 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 322, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 98 37 25 148 36 322 450 322), lower := (rows 11 98 37 25 148 36 64 128 256), losses := [] }

theorem u14618 : Upper (D 6) (R 6) [10,96,33,17,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14619 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 25 148 96 326 390 262), lower := (rows 11 98 37 25 148 96 64 128 256), losses := [] }

theorem u14619 : Upper (D 6) (R 6) [10,96,33,17,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14620 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 98 37 25 148 288 70 198 326), lower := (rows 11 98 37 25 148 288 64 128 256), losses := [] }

theorem u14620 : Upper (D 6) (R 6) [10,96,33,17,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14620 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14621 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 25 400 34 68 196 324), lower := (rows 11 98 37 25 400 34 64 128 256), losses := [] }

theorem u14621 : Upper (D 6) (R 6) [10,96,33,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14622 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 98 37 25 400 36 70 198 326), lower := (rows 11 98 37 25 400 36 64 128 256), losses := [] }

theorem u14622 : Upper (D 6) (R 6) [10,96,33,17,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14623 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 25 400 96 70 134 262), lower := (rows 11 98 37 25 400 96 64 128 256), losses := [] }

theorem u14623 : Upper (D 6) (R 6) [10,96,33,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14624 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 28 145 34 324 452 324), lower := (rows 11 98 37 28 145 34 64 128 256), losses := [] }

theorem u14624 : Upper (D 6) (R 6) [10,96,33,20,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14625 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 44, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 98 37 28 145 36 322 450 322), lower := (rows 11 98 37 28 145 36 64 128 256), losses := [] }

theorem u14625 : Upper (D 6) (R 6) [10,96,33,20,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14626 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 28 145 96 326 390 262), lower := (rows 11 98 37 28 145 96 64 128 256), losses := [] }

theorem u14626 : Upper (D 6) (R 6) [10,96,33,20,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14627 : Route 9 := (fun mask => (mask,id))

def c14627 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14627 : Upper (D 6) (R 6) [10,96,33,20,129,256] 13 := by
  apply FastRouting.sound _ _ [10,96,33,20,129,256] 13 (by decide) (choices 1) [2,4] r14627 c14627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3324
  · exact u3325

def b14628 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 28 146 33 324 452 324), lower := (rows 11 98 37 28 146 33 64 128 256), losses := [] }

theorem u14628 : Upper (D 6) (R 6) [10,96,33,20,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14629 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 28 146 36 321 449 321), lower := (rows 11 98 37 28 146 36 64 128 256), losses := [] }

theorem u14629 : Upper (D 6) (R 6) [10,96,33,20,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14630 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 28 146 96 325 389 261), lower := (rows 11 98 37 28 146 96 64 128 256), losses := [] }

theorem u14630 : Upper (D 6) (R 6) [10,96,33,20,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14631 : Route 9 := (fun mask => (mask,id))

def c14631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14631 : Upper (D 6) (R 6) [10,96,33,20,130,256] 13 := by
  apply FastRouting.sound _ _ [10,96,33,20,130,256] 13 (by decide) (choices 1) [1,4] r14631 c14631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3326
  · exact u3327

def b14632 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 28 208 33 326 390 262), lower := (rows 11 98 37 28 208 33 64 128 256), losses := [] }

theorem u14632 : Upper (D 6) (R 6) [10,96,33,20,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14633 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 28 208 34 325 389 261), lower := (rows 11 98 37 28 208 34 64 128 256), losses := [] }

theorem u14633 : Upper (D 6) (R 6) [10,96,33,20,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14633 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14634 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 98 37 28 208 36 323 387 259), lower := (rows 11 98 37 28 208 36 64 128 256), losses := [] }

theorem u14634 : Upper (D 6) (R 6) [10,96,33,20,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14634 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14635 : Route 9 := (fun mask => (mask,id))

def c14635 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14635 : Upper (D 6) (R 6) [10,96,33,20,192,256] 13 := by
  apply FastRouting.sound _ _ [10,96,33,20,192,256] 13 (by decide) (choices 1) [1,2,4] r14635 c14635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3328
  · exact u3329
  · exact u3330

def b14636 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 98 37 28 400 33 70 198 326), lower := (rows 11 98 37 28 400 33 64 128 256), losses := [] }

theorem u14636 : Upper (D 6) (R 6) [10,96,33,20,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14637 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 98 37 28 400 34 69 197 325), lower := (rows 11 98 37 28 400 34 64 128 256), losses := [] }

theorem u14637 : Upper (D 6) (R 6) [10,96,33,20,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14638 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 464, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 98 37 28 400 36 67 195 323), lower := (rows 11 98 37 28 400 36 64 128 256), losses := [] }

theorem u14638 : Upper (D 6) (R 6) [10,96,33,20,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14639 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 98 37 28 400 96 71 135 263), lower := (rows 11 98 37 28 400 96 64 128 256), losses := [] }

theorem u14639 : Upper (D 6) (R 6) [10,96,33,20,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14639
end Delivery.IrregularNine14.P06
