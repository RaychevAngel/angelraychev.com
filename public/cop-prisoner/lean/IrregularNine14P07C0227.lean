import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0034

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13620 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 324 88 176 160 67 131 259), lower := (rows 7 42 324 88 176 160 64 128 256), losses := [] }

theorem u13620 : Upper (D 7) (R 7) [6,40,320,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13621 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 7 42 324 137 49 34 208 208 464), lower := (rows 7 42 324 137 49 34 64 128 256), losses := [] }

theorem u13621 : Upper (D 7) (R 7) [6,40,320,129,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13622 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 50, targets := 192 }], pairs := [(1,6),(1,7),(4,6)], upper := (rows 7 42 324 137 49 48 194 194 450), lower := (rows 7 42 324 137 49 48 64 128 256), losses := [] }

theorem u13622 : Upper (D 7) (R 7) [6,40,320,129,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13622 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13623 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 138, targets := 64 }], pairs := [(1,6),(3,6),(4,1),(4,7)], upper := (rows 7 42 324 137 49 96 210 146 402), lower := (rows 7 42 324 137 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 100 64 128 256), good := (rows 53 40 356 153 49 96 96 128 256) },{ target := 7, region := (rows 1 2 4 8 17 100 64 0 256), good := (rows 55 42 356 25 49 96 96 0 256) }] }

theorem u13623 : Upper (D 7) (R 7) [6,40,320,129,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13623 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13624 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(4,7)], upper := (rows 7 42 324 137 49 160 82 210 338), lower := (rows 7 42 324 137 49 160 64 128 256), losses := [] }

theorem u13624 : Upper (D 7) (R 7) [6,40,320,129,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13625 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 4, region := 170, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 7 42 324 137 81 34 240 176 432), lower := (rows 7 42 324 137 81 34 64 128 256), losses := [] }

theorem u13625 : Upper (D 7) (R 7) [6,40,320,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13625 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13626 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 170, targets := 64 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,6),(2,0),(3,6)], upper := (rows 7 42 324 137 81 48 226 162 418), lower := (rows 7 42 324 137 81 48 64 128 256), losses := [] }

theorem u13626 : Upper (D 7) (R 7) [6,40,320,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13626 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13627 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 324 137 81 160 114 178 306), lower := (rows 7 42 324 137 81 160 64 128 256), losses := [] }

theorem u13627 : Upper (D 7) (R 7) [6,40,320,129,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13628 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 324 137 82 33 240 176 432), lower := (rows 7 42 324 137 82 33 64 128 256), losses := [] }

theorem u13628 : Upper (D 7) (R 7) [6,40,320,129,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13629 : Route 9 := (fun mask => (mask,id))

def c13629 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13629 : Upper (D 7) (R 7) [6,40,320,129,66,16] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,66,16] 13 (by decide) (choices 1) [1,32,128] r13629 c13629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2041
  · exact u2042
  · exact u2043

def b13630 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 324 137 82 160 113 177 305), lower := (rows 7 42 324 137 82 160 64 128 256), losses := [] }

theorem u13630 : Upper (D 7) (R 7) [6,40,320,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13631 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 324 137 112 33 210 146 402), lower := (rows 7 42 324 137 112 33 64 128 256), losses := [] }

theorem u13631 : Upper (D 7) (R 7) [6,40,320,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13632 : Route 9 := (fun mask => (mask,id))

def c13632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13632 : Upper (D 7) (R 7) [6,40,320,129,96,2] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,96,2] 13 (by decide) (choices 1) [1,16,128] r13632 c13632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2044
  · exact u2045
  · exact u2046

def b13633 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 324 137 112 48 195 131 387), lower := (rows 7 42 324 137 112 48 64 128 256), losses := [] }

theorem u13633 : Upper (D 7) (R 7) [6,40,320,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13633 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13634 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 324 137 112 160 83 147 275), lower := (rows 7 42 324 137 112 160 64 128 256), losses := [] }

theorem u13634 : Upper (D 7) (R 7) [6,40,320,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13635 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6),(2,0),(4,0),(4,6)], upper := (rows 7 42 324 137 146 33 112 240 368), lower := (rows 7 42 324 137 146 33 64 128 256), losses := [] }

theorem u13635 : Upper (D 7) (R 7) [6,40,320,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13636 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 42 324 137 146 48 97 225 353), lower := (rows 7 42 324 137 146 48 64 128 256), losses := [] }

theorem u13636 : Upper (D 7) (R 7) [6,40,320,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13636 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13637 : Route 9 := (fun mask => (mask,id))

def c13637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13637 : Upper (D 7) (R 7) [6,40,320,129,130,64] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,130,64] 13 (by decide) (choices 1) [1,16,32] r13637 c13637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2047
  · exact u2048
  · exact u2049

def b13638 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6),(2,0),(4,0),(4,6)], upper := (rows 7 42 324 137 176 33 82 210 338), lower := (rows 7 42 324 137 176 33 64 128 256), losses := [] }

theorem u13638 : Upper (D 7) (R 7) [6,40,320,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13639 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 42 324 137 176 34 81 209 337), lower := (rows 7 42 324 137 176 34 64 128 256), losses := [] }

theorem u13639 : Upper (D 7) (R 7) [6,40,320,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13640 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 42 324 137 176 48 67 195 323), lower := (rows 7 42 324 137 176 48 64 128 256), losses := [] }

theorem u13640 : Upper (D 7) (R 7) [6,40,320,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13640 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13641 : Route 9 := (fun mask => (mask,id))

def c13641 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13641 : Upper (D 7) (R 7) [6,40,320,129,160,64] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,160,64] 13 (by decide) (choices 1) [1,2,16] r13641 c13641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2050
  · exact u2051
  · exact u2052

def b13642 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,6),(1,7),(2,0),(4,0)], upper := (rows 7 42 324 137 208 33 114 178 306), lower := (rows 7 42 324 137 208 33 64 128 256), losses := [] }

theorem u13642 : Upper (D 7) (R 7) [6,40,320,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13643 : Route 9 := (fun mask => (mask,id))

def c13643 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13643 : Upper (D 7) (R 7) [6,40,320,129,192,2] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,192,2] 13 (by decide) (choices 1) [1,16,32] r13643 c13643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2053
  · exact u2054
  · exact u2055

def r13644 : Route 9 := (fun mask => (mask,id))

def c13644 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13644 : Upper (D 7) (R 7) [6,40,320,129,192,16] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,192,16] 13 (by decide) (choices 1) [1,2,32] r13644 c13644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2056
  · exact u2057
  · exact u2058

def b13645 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(1,0),(2,0),(2,1),(3,0)], upper := (rows 7 42 324 138 49 33 208 208 464), lower := (rows 7 42 324 138 49 33 64 128 256), losses := [] }

theorem u13645 : Upper (D 7) (R 7) [6,40,320,130,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13646 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 324 138 49 48 193 193 449), lower := (rows 7 42 324 138 49 48 64 128 256), losses := [] }

theorem u13646 : Upper (D 7) (R 7) [6,40,320,130,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13646 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13647 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 138, targets := 64 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 42 324 138 49 96 209 145 401), lower := (rows 7 42 324 138 49 96 64 128 256), losses := [] }

theorem u13647 : Upper (D 7) (R 7) [6,40,320,130,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13648 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 324 138 49 160 81 209 337), lower := (rows 7 42 324 138 49 160 64 128 256), losses := [] }

theorem u13648 : Upper (D 7) (R 7) [6,40,320,130,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13649 : Route 9 := (fun mask => (mask,id))

def c13649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13649 : Upper (D 7) (R 7) [6,40,320,130,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,320,130,96,1] 13 (by decide) (choices 1) [1,16,128] r13649 c13649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2059
  · exact u2060
  · exact u2061

def b13650 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 324 138 112 48 193 129 385), lower := (rows 7 42 324 138 112 48 64 128 256), losses := [] }

theorem u13650 : Upper (D 7) (R 7) [6,40,320,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13650 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13651 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 324 138 112 160 81 145 273), lower := (rows 7 42 324 138 112 160 64 128 256), losses := [] }

theorem u13651 : Upper (D 7) (R 7) [6,40,320,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13652 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 42, targets := 64 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 42 324 138 145 33 112 240 368), lower := (rows 7 42 324 138 145 33 64 128 256), losses := [] }

theorem u13652 : Upper (D 7) (R 7) [6,40,320,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13653 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 7 42 324 138 145 48 97 225 353), lower := (rows 7 42 324 138 145 48 64 128 256), losses := [] }

theorem u13653 : Upper (D 7) (R 7) [6,40,320,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13653 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13654 : Route 9 := (fun mask => (mask,id))

def c13654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13654 : Upper (D 7) (R 7) [6,40,320,130,129,64] 13 := by
  apply FastRouting.sound _ _ [6,40,320,130,129,64] 13 (by decide) (choices 1) [1,16,32] r13654 c13654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2062
  · exact u2063
  · exact u2064

def r13655 : Route 9 := (fun mask => (mask,id))

def c13655 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13655 : Upper (D 7) (R 7) [6,40,320,130,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,320,130,192,1] 13 (by decide) (choices 1) [1,16,32] r13655 c13655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2065
  · exact u2066
  · exact u2067

def b13656 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 7 42 324 138 208 48 97 161 289), lower := (rows 7 42 324 138 208 48 64 128 256), losses := [] }

theorem u13656 : Upper (D 7) (R 7) [6,40,320,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13656 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13657 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 7 42 324 152 49 33 194 194 450), lower := (rows 7 42 324 152 49 33 64 128 256), losses := [] }

theorem u13657 : Upper (D 7) (R 7) [6,40,320,144,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13658 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 42 324 152 49 34 193 193 449), lower := (rows 7 42 324 152 49 34 64 128 256), losses := [] }

theorem u13658 : Upper (D 7) (R 7) [6,40,320,144,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13658 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13659 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 4, region := 138, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,6)], upper := (rows 7 42 324 152 49 96 195 131 387), lower := (rows 7 42 324 152 49 96 64 128 256), losses := [] }

theorem u13659 : Upper (D 7) (R 7) [6,40,320,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13660 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(0,7),(2,7),(4,7)], upper := (rows 7 42 324 152 49 160 67 195 323), lower := (rows 7 42 324 152 49 160 64 128 256), losses := [] }

theorem u13660 : Upper (D 7) (R 7) [6,40,320,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13661 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 170, targets := 64 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(3,6)], upper := (rows 7 42 324 152 81 33 226 162 418), lower := (rows 7 42 324 152 81 33 64 128 256), losses := [{ target := 7, region := (rows 1 10 4 8 16 49 64 0 256), good := (rows 39 42 324 58 113 33 64 0 256) }] }

theorem u13661 : Upper (D 7) (R 7) [6,40,320,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13662 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 4, region := 170, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,6)], upper := (rows 7 42 324 152 81 34 225 161 417), lower := (rows 7 42 324 152 81 34 64 128 256), losses := [] }

theorem u13662 : Upper (D 7) (R 7) [6,40,320,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13663 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 324 152 81 160 99 163 291), lower := (rows 7 42 324 152 81 160 64 128 256), losses := [] }

theorem u13663 : Upper (D 7) (R 7) [6,40,320,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13664 : Route 9 := (fun mask => (mask,id))

def c13664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13664 : Upper (D 7) (R 7) [6,40,320,144,66,1] 13 := by
  apply FastRouting.sound _ _ [6,40,320,144,66,1] 13 (by decide) (choices 1) [1,32,128] r13664 c13664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2068
  · exact u2069
  · exact u2070

def b13665 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 324 152 82 160 97 161 289), lower := (rows 7 42 324 152 82 160 64 128 256), losses := [] }

theorem u13665 : Upper (D 7) (R 7) [6,40,320,144,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13666 : Route 9 := (fun mask => (mask,id))

def c13666 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13666 : Upper (D 7) (R 7) [6,40,320,144,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,320,144,96,1] 13 (by decide) (choices 1) [1,2,128] r13666 c13666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2071
  · exact u2072
  · exact u2073

def b13667 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 452, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 324 152 112 34 193 129 385), lower := (rows 7 42 324 152 112 34 64 128 256), losses := [] }

theorem u13667 : Upper (D 7) (R 7) [6,40,320,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13667 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13668 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(0,7),(2,7),(4,7)], upper := (rows 7 42 324 152 112 160 67 131 259), lower := (rows 7 42 324 152 112 160 64 128 256), losses := [] }

theorem u13668 : Upper (D 7) (R 7) [6,40,320,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13669 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 462, targets := 1 },{ cop := 5, region := 16, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 42 324 200 49 33 210 146 402), lower := (rows 7 42 324 200 49 33 64 128 256), losses := [] }

theorem u13669 : Upper (D 7) (R 7) [6,40,320,192,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13670 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 7 42 324 200 49 34 209 145 401), lower := (rows 7 42 324 200 49 34 64 128 256), losses := [] }

theorem u13670 : Upper (D 7) (R 7) [6,40,320,192,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13671 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 324 200 49 48 195 131 387), lower := (rows 7 42 324 200 49 48 64 128 256), losses := [] }

theorem u13671 : Upper (D 7) (R 7) [6,40,320,192,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13671 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13672 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 324 200 49 160 83 147 275), lower := (rows 7 42 324 200 49 160 64 128 256), losses := [] }

theorem u13672 : Upper (D 7) (R 7) [6,40,320,192,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13673 : Route 9 := (fun mask => (mask,id))

def c13673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13673 : Upper (D 7) (R 7) [6,40,320,192,129,1] 13 := by
  apply FastRouting.sound _ _ [6,40,320,192,129,1] 13 (by decide) (choices 1) [2,16,32] r13673 c13673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2074
  · exact u2075
  · exact u2076

def b13674 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 176, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 7 42 324 200 145 34 113 177 305), lower := (rows 7 42 324 200 145 34 64 128 256), losses := [] }

theorem u13674 : Upper (D 7) (R 7) [6,40,320,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13675 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 0, region := 176, targets := 64 }], pairs := [(0,7),(2,7),(4,6)], upper := (rows 7 42 324 200 145 48 99 163 291), lower := (rows 7 42 324 200 145 48 64 128 256), losses := [] }

theorem u13675 : Upper (D 7) (R 7) [6,40,320,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13675 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13676 : Route 9 := (fun mask => (mask,id))

def c13676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13676 : Upper (D 7) (R 7) [6,40,320,192,130,1] 13 := by
  apply FastRouting.sound _ _ [6,40,320,192,130,1] 13 (by decide) (choices 1) [1,16,32] r13676 c13676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2077
  · exact u2078
  · exact u2079

def b13677 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 42 324 200 146 48 97 161 289), lower := (rows 7 42 324 200 146 48 64 128 256), losses := [] }

theorem u13677 : Upper (D 7) (R 7) [6,40,320,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13677 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13678 : Route 9 := (fun mask => (mask,id))

def c13678 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13678 : Upper (D 7) (R 7) [6,40,320,192,160,1] 13 := by
  apply FastRouting.sound _ _ [6,40,320,192,160,1] 13 (by decide) (choices 1) [1,2,16] r13678 c13678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2080
  · exact u2081
  · exact u2082

def b13679 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 42 324 200 176 34 81 145 273), lower := (rows 7 42 324 200 176 34 64 128 256), losses := [] }

theorem u13679 : Upper (D 7) (R 7) [6,40,320,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13679
end Delivery.IrregularNine14.P07
