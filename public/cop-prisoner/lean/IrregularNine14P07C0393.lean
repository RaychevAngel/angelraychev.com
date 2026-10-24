import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0125
import IrregularNine14P07C0126

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23580 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 266 208 33 210 146 402), lower := (rows 37 98 13 266 208 33 64 128 256), losses := [] }

theorem u23580 : Upper (D 7) (R 7) [36,96,9,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23581 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 13 266 208 34 209 145 401), lower := (rows 37 98 13 266 208 34 64 128 256), losses := [] }

theorem u23581 : Upper (D 7) (R 7) [36,96,9,258,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23582 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 13 266 208 48 195 131 387), lower := (rows 37 98 13 266 208 48 64 128 256), losses := [] }

theorem u23582 : Upper (D 7) (R 7) [36,96,9,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23582 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23583 : Route 9 := (fun mask => (mask,id))

def c23583 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23583 : Upper (D 7) (R 7) [36,96,9,258,192,128] 13 := by
  apply FastRouting.sound _ _ [36,96,9,258,192,128] 13 (by decide) (choices 1) [1,2,16] r23583 c23583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7545
  · exact u7546
  · exact u7547

def b23584 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 4, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(3,0)], upper := (rows 37 98 13 280 81 34 194 130 386), lower := (rows 37 98 13 280 81 34 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 9 17 0 98 162 290), good := (rows 477 450 29 284 93 450 64 128 256) }] }

theorem u23584 : Upper (D 7) (R 7) [36,96,9,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23584 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23585 : Route 9 := (fun mask => (mask,id))

def c23585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23585 : Upper (D 7) (R 7) [36,96,9,272,65,128] 13 := by
  apply FastRouting.sound _ _ [36,96,9,272,65,128] 13 (by decide) (choices 1) [2,128] r23585 c23585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7548
  · exact u7549

def b23586 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(3,0)], upper := (rows 37 98 13 280 145 34 194 194 450), lower := (rows 37 98 13 280 145 34 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 9 17 0 98 162 290), good := (rows 477 450 29 284 157 450 64 128 256) }] }

theorem u23586 : Upper (D 7) (R 7) [36,96,9,272,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23587 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 280 145 96 194 130 386), lower := (rows 37 98 13 280 145 96 64 128 256), losses := [] }

theorem u23587 : Upper (D 7) (R 7) [36,96,9,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23587 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23588 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 37 98 13 280 145 160 66 194 322), lower := (rows 37 98 13 280 145 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 96 13 317 177 160 64 160 256) }] }

theorem u23588 : Upper (D 7) (R 7) [36,96,9,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23589 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 280 146 33 194 194 450), lower := (rows 37 98 13 280 146 33 64 128 256), losses := [] }

theorem u23589 : Upper (D 7) (R 7) [36,96,9,272,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23589 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23590 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 13 280 146 34 193 193 449), lower := (rows 37 98 13 280 146 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 128 256), good := (rows 37 34 13 317 178 34 0 128 256) }] }

theorem u23590 : Upper (D 7) (R 7) [36,96,9,272,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23591 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 280 146 96 195 131 387), lower := (rows 37 98 13 280 146 96 64 128 256), losses := [] }

theorem u23591 : Upper (D 7) (R 7) [36,96,9,272,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23592 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(2,1)], upper := (rows 37 98 13 280 146 160 67 195 323), lower := (rows 37 98 13 280 146 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 96 13 317 176 160 64 160 256) },{ target := 6, region := (rows 9 2 12 8 16 176 0 128 256), good := (rows 37 34 13 317 178 160 0 160 256) }] }

theorem u23592 : Upper (D 7) (R 7) [36,96,9,272,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23593 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 280 208 33 194 130 386), lower := (rows 37 98 13 280 208 33 64 128 256), losses := [] }

theorem u23593 : Upper (D 7) (R 7) [36,96,9,272,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23594 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 34, targets := 129 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 280 208 34 195 131 387), lower := (rows 37 98 13 280 208 34 64 128 256), losses := [{ target := 7, region := (rows 13 82 12 8 16 122 64 0 256), good := (rows 37 98 45 319 114 34 98 0 256) }] }

theorem u23594 : Upper (D 7) (R 7) [36,96,9,272,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23595 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 66, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(2,1)], upper := (rows 37 98 13 280 208 160 67 131 259), lower := (rows 37 98 13 280 208 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 37 96 13 317 240 160 64 160 256) }] }

theorem u23595 : Upper (D 7) (R 7) [36,96,9,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23596 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 328 145 34 210 146 402), lower := (rows 37 98 13 328 145 34 64 128 256), losses := [] }

theorem u23596 : Upper (D 7) (R 7) [36,96,9,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23597 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 458, targets := 1 },{ cop := 1, region := 392, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 98 13 328 145 48 194 130 386), lower := (rows 37 98 13 328 145 48 64 128 256), losses := [] }

theorem u23597 : Upper (D 7) (R 7) [36,96,9,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23597 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23598 : Route 9 := (fun mask => (mask,id))

def c23598 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23598 : Upper (D 7) (R 7) [36,96,9,320,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,9,320,129,128] 13 (by decide) (choices 1) [2,16] r23598 c23598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7550
  · exact u7551

def b23599 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 98 13 328 146 33 210 146 402), lower := (rows 37 98 13 328 146 33 64 128 256), losses := [] }

theorem u23599 : Upper (D 7) (R 7) [36,96,9,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23600 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 13 328 146 34 209 145 401), lower := (rows 37 98 13 328 146 34 64 128 256), losses := [] }

theorem u23600 : Upper (D 7) (R 7) [36,96,9,320,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23601 : Route 9 := (fun mask => (mask,id))

def c23601 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23601 : Upper (D 7) (R 7) [36,96,9,320,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,9,320,130,16] 13 (by decide) (choices 1) [1,2,128] r23601 c23601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7552
  · exact u7553
  · exact u7554

def r23602 : Route 9 := (fun mask => (mask,id))

def c23602 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23602 : Upper (D 7) (R 7) [36,96,9,320,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,9,320,130,128] 13 (by decide) (choices 1) [1,2,16] r23602 c23602
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7555
  · exact u7556
  · exact u7557

def r23603 : Route 9 := (fun mask => (mask,id))

def c23603 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23603 : Upper (D 7) (R 7) [36,96,9,384,65,2] 13 := by
  apply FastRouting.sound _ _ [36,96,9,384,65,2] 13 (by decide) (choices 1) [2,16,128] r23603 c23603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7558
  · exact u7559
  · exact u7560

def b23604 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 13 392 81 48 194 130 386), lower := (rows 37 98 13 392 81 48 64 128 256), losses := [] }

theorem u23604 : Upper (D 7) (R 7) [36,96,9,384,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23604 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23605 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 13 392 81 160 82 146 274), lower := (rows 37 98 13 392 81 160 64 128 256), losses := [] }

theorem u23605 : Upper (D 7) (R 7) [36,96,9,384,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23605 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23606 : Route 9 := (fun mask => (mask,id))

def c23606 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23606 : Upper (D 7) (R 7) [36,96,9,384,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,9,384,129,2] 13 (by decide) (choices 1) [2,16] r23606 c23606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7561
  · exact u7562

def b23607 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 53, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 98 13 392 145 48 66 194 322), lower := (rows 37 98 13 392 145 48 64 128 256), losses := [] }

theorem u23607 : Upper (D 7) (R 7) [36,96,9,384,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23607 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23608 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 392 145 96 82 146 274), lower := (rows 37 98 13 392 145 96 64 128 256), losses := [] }

theorem u23608 : Upper (D 7) (R 7) [36,96,9,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23608 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23609 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 392 146 33 82 210 338), lower := (rows 37 98 13 392 146 33 64 128 256), losses := [] }

theorem u23609 : Upper (D 7) (R 7) [36,96,9,384,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23610 : Route 9 := (fun mask => (mask,id))

def c23610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23610 : Upper (D 7) (R 7) [36,96,9,384,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,9,384,130,2] 13 (by decide) (choices 1) [1,16] r23610 c23610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7563
  · exact u7564

def r23611 : Route 9 := (fun mask => (mask,id))

def c23611 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23611 : Upper (D 7) (R 7) [36,96,9,384,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,9,384,130,16] 13 (by decide) (choices 1) [1,2] r23611 c23611
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7565
  · exact u7566

def b23612 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 13 392 146 96 83 147 275), lower := (rows 37 98 13 392 146 96 64 128 256), losses := [] }

theorem u23612 : Upper (D 7) (R 7) [36,96,9,384,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23613 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 13 392 208 33 82 146 274), lower := (rows 37 98 13 392 208 33 64 128 256), losses := [] }

theorem u23613 : Upper (D 7) (R 7) [36,96,9,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23614 : Route 9 := (fun mask => (mask,id))

def c23614 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23614 : Upper (D 7) (R 7) [36,96,9,384,192,2] 13 := by
  apply FastRouting.sound _ _ [36,96,9,384,192,2] 13 (by decide) (choices 1) [1,2,16] r23614 c23614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7567
  · exact u7568
  · exact u7569

def b23615 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 13 392 208 48 67 131 259), lower := (rows 37 98 13 392 208 48 64 128 256), losses := [] }

theorem u23615 : Upper (D 7) (R 7) [36,96,9,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23615 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23616 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 14 25 146 33 448 448 448), lower := (rows 37 98 14 25 146 33 64 128 256), losses := [] }

theorem u23616 : Upper (D 7) (R 7) [36,96,10,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23616 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23617 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 25 146 96 449 385 385), lower := (rows 37 98 14 25 146 96 64 128 256), losses := [] }

theorem u23617 : Upper (D 7) (R 7) [36,96,10,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23618 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,6),(1,7),(2,6),(3,6)], upper := (rows 37 98 14 25 146 160 321 449 321), lower := (rows 37 98 14 25 146 160 64 128 256), losses := [] }

theorem u23618 : Upper (D 7) (R 7) [36,96,10,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23619 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 481, targets := 2 }], pairs := [(0,1),(3,5),(4,5)], upper := (rows 37 98 14 25 146 288 193 193 449), lower := (rows 37 98 14 25 146 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 20 0 73 137 265), good := (rows 477 66 478 473 146 256 64 128 256) }] }

theorem u23619 : Upper (D 7) (R 7) [36,96,10,17,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23619 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23620 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 98 14 25 208 33 450 386 386), lower := (rows 37 98 14 25 208 33 64 128 256), losses := [] }

theorem u23620 : Upper (D 7) (R 7) [36,96,10,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23621 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 25 208 34 449 385 385), lower := (rows 37 98 14 25 208 34 64 128 256), losses := [] }

theorem u23621 : Upper (D 7) (R 7) [36,96,10,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23622 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 322, targets := 128 },{ cop := 2, region := 417, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(1,7),(2,0)], upper := (rows 37 98 14 25 208 160 323 387 259), lower := (rows 37 98 14 25 208 160 64 128 256), losses := [{ target := 0, region := (rows 0 18 12 8 16 176 64 128 256), good := (rows 36 98 14 62 242 160 64 160 256) }] }

theorem u23622 : Upper (D 7) (R 7) [36,96,10,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23623 : Route 9 := (fun mask => (mask,id))

def c23623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23623 : Upper (D 7) (R 7) [36,96,10,17,192,256] 13 := by
  apply FastRouting.sound _ _ [36,96,10,17,192,256] 13 (by decide) (choices 1) [1,2,128] r23623 c23623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7570
  · exact u7571
  · exact u7572

def b23624 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 98 14 25 274 33 192 192 448), lower := (rows 37 98 14 25 274 33 64 128 256), losses := [] }

theorem u23624 : Upper (D 7) (R 7) [36,96,10,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23625 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 25 274 96 193 129 385), lower := (rows 37 98 14 25 274 96 64 128 256), losses := [] }

theorem u23625 : Upper (D 7) (R 7) [36,96,10,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23626 : Route 9 := (fun mask => (mask,id))

def c23626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23626 : Upper (D 7) (R 7) [36,96,10,17,258,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,17,258,128] 13 (by decide) (choices 1) [1,128] r23626 c23626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7573
  · exact u7574

def b23627 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 98 14 25 336 33 194 130 386), lower := (rows 37 98 14 25 336 33 64 128 256), losses := [] }

theorem u23627 : Upper (D 7) (R 7) [36,96,10,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23628 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 25 336 34 193 129 385), lower := (rows 37 98 14 25 336 34 64 128 256), losses := [] }

theorem u23628 : Upper (D 7) (R 7) [36,96,10,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23629 : Route 9 := (fun mask => (mask,id))

def c23629 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23629 : Upper (D 7) (R 7) [36,96,10,17,320,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,17,320,128] 13 (by decide) (choices 1) [1,2,128] r23629 c23629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7575
  · exact u7576
  · exact u7577

def b23630 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 14 25 400 33 194 194 450), lower := (rows 37 98 14 25 400 33 64 128 256), losses := [] }

theorem u23630 : Upper (D 7) (R 7) [36,96,10,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23631 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 25 400 34 193 193 449), lower := (rows 37 98 14 25 400 34 64 128 256), losses := [] }

theorem u23631 : Upper (D 7) (R 7) [36,96,10,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23632 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 14 25 400 96 195 131 387), lower := (rows 37 98 14 25 400 96 64 128 256), losses := [] }

theorem u23632 : Upper (D 7) (R 7) [36,96,10,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23633 : Route 9 := (fun mask => (mask,id))

def c23633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23633 : Upper (D 7) (R 7) [36,96,10,17,384,128] 13 := by
  apply FastRouting.sound _ _ [36,96,10,17,384,128] 13 (by decide) (choices 1) [1,2] r23633 c23633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7578
  · exact u7579

def b23634 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 88 145 33 450 386 386), lower := (rows 37 98 14 88 145 33 64 128 256), losses := [] }

theorem u23634 : Upper (D 7) (R 7) [36,96,10,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23635 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 14 88 145 34 449 385 385), lower := (rows 37 98 14 88 145 34 64 128 256), losses := [] }

theorem u23635 : Upper (D 7) (R 7) [36,96,10,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23636 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 322, targets := 128 }], pairs := [(0,6),(1,0),(1,7),(4,6)], upper := (rows 37 98 14 88 145 160 323 387 259), lower := (rows 37 98 14 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 176 64 128 256), good := (rows 36 98 14 126 176 160 64 160 256) }] }

theorem u23636 : Upper (D 7) (R 7) [36,96,10,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23637 : Route 9 := (fun mask => (mask,id))

def c23637 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23637 : Upper (D 7) (R 7) [36,96,10,80,129,256] 13 := by
  apply FastRouting.sound _ _ [36,96,10,80,129,256] 13 (by decide) (choices 1) [1,2,128] r23637 c23637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7580
  · exact u7581
  · exact u7582

def b23638 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 14 88 146 33 449 385 385), lower := (rows 37 98 14 88 146 33 64 128 256), losses := [] }

theorem u23638 : Upper (D 7) (R 7) [36,96,10,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23639 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 433, targets := 64 },{ cop := 0, region := 322, targets := 128 },{ cop := 2, region := 417, targets := 2 }], pairs := [(0,1),(0,6),(1,7),(4,6)], upper := (rows 37 98 14 88 146 160 321 385 257), lower := (rows 37 98 14 88 146 160 64 128 256), losses := [] }

theorem u23639 : Upper (D 7) (R 7) [36,96,10,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u23639
end Delivery.IrregularNine14.P07
