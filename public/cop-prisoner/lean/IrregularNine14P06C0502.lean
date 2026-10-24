import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0194
import IrregularNine14P06C0195

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30120 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 294, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 22 38 137 81 356 356 484 356), lower := (rows 11 22 38 137 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 38 70 134 262), good := (rows 505 500 484 153 89 32 64 128 256) }] }

theorem u30120 : Upper (D 6) (R 6) [10,20,34,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30120 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30121 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 38 137 84 353 353 481 353), lower := (rows 11 22 38 137 84 32 64 128 256), losses := [] }

theorem u30121 : Upper (D 6) (R 6) [10,20,34,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30122 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 137 112 357 325 453 325), lower := (rows 11 22 38 137 112 32 64 128 256), losses := [] }

theorem u30122 : Upper (D 6) (R 6) [10,20,34,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30122 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30123 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 22 38 137 273 100 100 228 356), lower := (rows 11 22 38 137 273 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 38 70 134 262), good := (rows 505 500 484 153 281 32 64 128 256) }] }

theorem u30123 : Upper (D 6) (R 6) [10,20,34,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30123 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30124 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 38 137 276 97 97 225 353), lower := (rows 11 22 38 137 276 32 64 128 256), losses := [] }

theorem u30124 : Upper (D 6) (R 6) [10,20,34,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30124 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30125 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 137 304 101 69 197 325), lower := (rows 11 22 38 137 304 32 64 128 256), losses := [] }

theorem u30125 : Upper (D 6) (R 6) [10,20,34,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30125 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30126 : Route 9 := (fun mask => (mask,id))

def c30126 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30126 : Upper (D 6) (R 6) [10,20,34,129,320] 13 := by
  apply FastRouting.sound _ _ [10,20,34,129,320] 13 (by decide) (choices 1) [1,4,64] r30126 c30126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11659
  · exact u11660
  · exact u11661

def b30127 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 140 49 353 321 449 321), lower := (rows 11 22 38 140 49 32 64 128 256), losses := [] }

theorem u30127 : Upper (D 6) (R 6) [10,20,34,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30127 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30128 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 22 38 140 81 353 353 481 353), lower := (rows 11 22 38 140 81 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 17 49 81 145 273), good := (rows 505 508 44 140 497 32 64 128 256) }] }

theorem u30128 : Upper (D 6) (R 6) [10,20,34,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30129 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 140 112 353 321 449 321), lower := (rows 11 22 38 140 112 32 64 128 256), losses := [] }

theorem u30129 : Upper (D 6) (R 6) [10,20,34,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30130 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 22 38 140 273 97 97 225 353), lower := (rows 11 22 38 140 273 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 10 17 49 81 145 273), good := (rows 505 508 44 140 497 32 64 128 256) }] }

theorem u30130 : Upper (D 6) (R 6) [10,20,34,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30131 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 140 304 97 65 193 321), lower := (rows 11 22 38 140 304 32 64 128 256), losses := [] }

theorem u30131 : Upper (D 6) (R 6) [10,20,34,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30132 : Route 9 := (fun mask => (mask,id))

def c30132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30132 : Upper (D 6) (R 6) [10,20,34,132,320] 13 := by
  apply FastRouting.sound _ _ [10,20,34,132,320] 13 (by decide) (choices 1) [1,64] r30132 c30132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11662
  · exact u11663

def b30133 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 23, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 22 38 168 21 353 321 449 321), lower := (rows 11 22 38 168 21 32 64 128 256), losses := [] }

theorem u30133 : Upper (D 6) (R 6) [10,20,34,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30134 : Route 9 := (fun mask => (mask,id))

def c30134 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30134 : Upper (D 6) (R 6) [10,20,34,160,65] 13 := by
  apply FastRouting.sound _ _ [10,20,34,160,65] 13 (by decide) (choices 1) [1,4,64,256] r30134 c30134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11664
  · exact u11665
  · exact u11666
  · exact u11667

def b30135 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 38 168 84 353 321 449 321), lower := (rows 11 22 38 168 84 32 64 128 256), losses := [] }

theorem u30135 : Upper (D 6) (R 6) [10,20,34,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30135 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30136 : Route 9 := (fun mask => (mask,id))

def c30136 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30136 : Upper (D 6) (R 6) [10,20,34,160,257] 13 := by
  apply FastRouting.sound _ _ [10,20,34,160,257] 13 (by decide) (choices 1) [1,4,64] r30136 c30136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11668
  · exact u11669
  · exact u11670

def b30137 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 38 168 276 97 65 193 321), lower := (rows 11 22 38 168 276 32 64 128 256), losses := [] }

theorem u30137 : Upper (D 6) (R 6) [10,20,34,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30137 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30138 : Route 9 := (fun mask => (mask,id))

def c30138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30138 : Upper (D 6) (R 6) [10,20,34,160,320] 13 := by
  apply FastRouting.sound _ _ [10,20,34,160,320] 13 (by decide) (choices 1) [1,4,64] r30138 c30138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11671
  · exact u11672
  · exact u11673

def b30139 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 38 200 21 353 353 481 353), lower := (rows 11 22 38 200 21 32 64 128 256), losses := [] }

theorem u30139 : Upper (D 6) (R 6) [10,20,34,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30140 : PairBound 9 := { available := 325, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 200 49 357 325 453 325), lower := (rows 11 22 38 200 49 32 64 128 256), losses := [] }

theorem u30140 : Upper (D 6) (R 6) [10,20,34,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30141 : PairBound 9 := { available := 321, camps := [{ cop := 5, region := 22, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 200 52 353 321 449 321), lower := (rows 11 22 38 200 52 32 64 128 256), losses := [] }

theorem u30141 : Upper (D 6) (R 6) [10,20,34,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30141 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30142 : Route 9 := (fun mask => (mask,id))

def c30142 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30142 : Upper (D 6) (R 6) [10,20,34,192,65] 13 := by
  apply FastRouting.sound _ _ [10,20,34,192,65] 13 (by decide) (choices 1) [1,4,256] r30142 c30142
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11674
  · exact u11675
  · exact u11676

def b30143 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 38 200 84 289 353 417 289), lower := (rows 11 22 38 200 84 32 64 128 256), losses := [] }

theorem u30143 : Upper (D 6) (R 6) [10,20,34,192,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30144 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 200 112 293 325 389 261), lower := (rows 11 22 38 200 112 32 64 128 256), losses := [] }

theorem u30144 : Upper (D 6) (R 6) [10,20,34,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30144 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30145 : Route 9 := (fun mask => (mask,id))

def c30145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30145 : Upper (D 6) (R 6) [10,20,34,192,257] 13 := by
  apply FastRouting.sound _ _ [10,20,34,192,257] 13 (by decide) (choices 1) [1,4,64] r30145 c30145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11677
  · exact u11678
  · exact u11679

def b30146 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 38 200 276 97 97 225 353), lower := (rows 11 22 38 200 276 32 64 128 256), losses := [] }

theorem u30146 : Upper (D 6) (R 6) [10,20,34,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30146 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30147 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 200 304 101 69 197 325), lower := (rows 11 22 38 200 304 32 64 128 256), losses := [] }

theorem u30147 : Upper (D 6) (R 6) [10,20,34,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30147 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30148 : Route 9 := (fun mask => (mask,id))

def c30148 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30148 : Upper (D 6) (R 6) [10,20,34,192,320] 13 := by
  apply FastRouting.sound _ _ [10,20,34,192,320] 13 (by decide) (choices 1) [1,4] r30148 c30148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11680
  · exact u11681

def b30149 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 38 392 21 97 97 225 353), lower := (rows 11 22 38 392 21 32 64 128 256), losses := [] }

theorem u30149 : Upper (D 6) (R 6) [10,20,34,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30150 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 392 49 101 69 197 325), lower := (rows 11 22 38 392 49 32 64 128 256), losses := [] }

theorem u30150 : Upper (D 6) (R 6) [10,20,34,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30151 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 22, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 392 52 97 65 193 321), lower := (rows 11 22 38 392 52 32 64 128 256), losses := [] }

theorem u30151 : Upper (D 6) (R 6) [10,20,34,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30151 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30152 : Route 9 := (fun mask => (mask,id))

def c30152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30152 : Upper (D 6) (R 6) [10,20,34,384,65] 13 := by
  apply FastRouting.sound _ _ [10,20,34,384,65] 13 (by decide) (choices 1) [1,4,64] r30152 c30152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11682
  · exact u11683
  · exact u11684

def b30153 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 38 392 84 97 97 225 353), lower := (rows 11 22 38 392 84 32 64 128 256), losses := [] }

theorem u30153 : Upper (D 6) (R 6) [10,20,34,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30154 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 392 112 101 69 197 325), lower := (rows 11 22 38 392 112 32 64 128 256), losses := [] }

theorem u30154 : Upper (D 6) (R 6) [10,20,34,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30155 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 100 41 19 484 452 452 452), lower := (rows 11 22 100 41 19 32 64 128 256), losses := [] }

theorem u30155 : Upper (D 6) (R 6) [10,20,96,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30155 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30156 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 22 100 41 21 482 450 450 450), lower := (rows 11 22 100 41 21 32 64 128 256), losses := [] }

theorem u30156 : Upper (D 6) (R 6) [10,20,96,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30157 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 18, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 22 100 41 22 481 449 449 449), lower := (rows 11 22 100 41 22 32 64 128 256), losses := [] }

theorem u30157 : Upper (D 6) (R 6) [10,20,96,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30157 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30158 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 4, region := 422, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 22 100 41 81 422 454 390 390), lower := (rows 11 22 100 41 81 32 64 128 256), losses := [] }

theorem u30158 : Upper (D 6) (R 6) [10,20,96,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30159 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 18, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 22 100 41 82 421 453 389 389), lower := (rows 11 22 100 41 82 32 64 128 256), losses := [] }

theorem u30159 : Upper (D 6) (R 6) [10,20,96,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30160 : PairBound 9 := { available := 387, camps := [{ cop := 2, region := 18, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 22 100 41 84 419 451 387 387), lower := (rows 11 22 100 41 84 32 64 128 256), losses := [] }

theorem u30160 : Upper (D 6) (R 6) [10,20,96,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30161 : PairBound 9 := { available := 326, camps := [{ cop := 4, region := 358, targets := 1 }], pairs := [(1,0),(2,0),(4,5)], upper := (rows 11 22 100 41 145 358 326 454 326), lower := (rows 11 22 100 41 145 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 66 130 258), good := (rows 475 470 68 25 145 0 64 128 256) }] }

theorem u30161 : Upper (D 6) (R 6) [10,20,96,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30162 : Route 9 := (fun mask => (mask,id))

def c30162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u30162 : Upper (D 6) (R 6) [10,20,96,33,130] 13 := by
  apply FastRouting.sound _ _ [10,20,96,33,130] 13 (by decide) (choices 1) [1,4,64,256] r30162 c30162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11685
  · exact u11686
  · exact u11687
  · exact u11688

def b30163 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 100 41 148 355 323 451 323), lower := (rows 11 22 100 41 148 32 64 128 256), losses := [] }

theorem u30163 : Upper (D 6) (R 6) [10,20,96,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30164 : Route 9 := (fun mask => (mask,id))

def c30164 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30164 : Upper (D 6) (R 6) [10,20,96,33,192] 13 := by
  apply FastRouting.sound _ _ [10,20,96,33,192] 13 (by decide) (choices 1) [1,2,4,256] r30164 c30164
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11689
  · exact u11690
  · exact u11691
  · exact u11692

def r30165 : Route 9 := (fun mask => (mask,id))

def c30165 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30165 : Upper (D 6) (R 6) [10,20,96,33,384] 13 := by
  apply FastRouting.sound _ _ [10,20,96,33,384] 13 (by decide) (choices 1) [1,2,4,64] r30165 c30165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11693
  · exact u11694
  · exact u11695
  · exact u11696

def b30166 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 22 100 137 19 356 356 484 356), lower := (rows 11 22 100 137 19 32 64 128 256), losses := [] }

theorem u30166 : Upper (D 6) (R 6) [10,20,96,129,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30167 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 489, targets := 4 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 22 100 137 21 354 354 482 354), lower := (rows 11 22 100 137 21 32 64 128 256), losses := [] }

theorem u30167 : Upper (D 6) (R 6) [10,20,96,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30168 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 100 137 22 353 353 481 353), lower := (rows 11 22 100 137 22 32 64 128 256), losses := [] }

theorem u30168 : Upper (D 6) (R 6) [10,20,96,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30169 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 4, region := 326, targets := 1 }], pairs := [(0,5),(1,0),(3,5)], upper := (rows 11 22 100 137 49 358 326 454 326), lower := (rows 11 22 100 137 49 32 64 128 256), losses := [] }

theorem u30169 : Upper (D 6) (R 6) [10,20,96,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30170 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 100 137 50 357 325 453 325), lower := (rows 11 22 100 137 50 32 64 128 256), losses := [] }

theorem u30170 : Upper (D 6) (R 6) [10,20,96,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30171 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 100 137 52 355 323 451 323), lower := (rows 11 22 100 137 52 32 64 128 256), losses := [] }

theorem u30171 : Upper (D 6) (R 6) [10,20,96,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30172 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 393, targets := 32 },{ cop := 1, region := 393, targets := 64 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 100 137 112 295 327 391 263), lower := (rows 11 22 100 137 112 32 64 128 256), losses := [] }

theorem u30172 : Upper (D 6) (R 6) [10,20,96,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30173 : Route 9 := (fun mask => (mask,id))

def c30173 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30173 : Upper (D 6) (R 6) [10,20,96,129,257] 13 := by
  apply FastRouting.sound _ _ [10,20,96,129,257] 13 (by decide) (choices 1) [2,4,64] r30173 c30173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11697
  · exact u11698
  · exact u11699

def r30174 : Route 9 := (fun mask => (mask,id))

def c30174 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30174 : Upper (D 6) (R 6) [10,20,96,129,258] 13 := by
  apply FastRouting.sound _ _ [10,20,96,129,258] 13 (by decide) (choices 1) [1,4,64] r30174 c30174
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11700
  · exact u11701
  · exact u11702

def b30175 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 2, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 11 22 100 137 276 99 99 227 355), lower := (rows 11 22 100 137 276 32 64 128 256), losses := [] }

theorem u30175 : Upper (D 6) (R 6) [10,20,96,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r30176 : Route 9 := (fun mask => (mask,id))

def c30176 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30176 : Upper (D 6) (R 6) [10,20,96,129,288] 13 := by
  apply FastRouting.sound _ _ [10,20,96,129,288] 13 (by decide) (choices 1) [1,2,4,64] r30176 c30176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11703
  · exact u11704
  · exact u11705
  · exact u11706

def b30177 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 19, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 22 100 140 19 353 353 481 353), lower := (rows 11 22 100 140 19 32 64 128 256), losses := [] }

theorem u30177 : Upper (D 6) (R 6) [10,20,96,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30178 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 22 100 140 49 355 323 451 323), lower := (rows 11 22 100 140 49 32 64 128 256), losses := [] }

theorem u30178 : Upper (D 6) (R 6) [10,20,96,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b30179 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 22 100 140 50 353 321 449 321), lower := (rows 11 22 100 140 50 32 64 128 256), losses := [] }

theorem u30179 : Upper (D 6) (R 6) [10,20,96,132,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b30179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u30179
end Delivery.IrregularNine14.P06
