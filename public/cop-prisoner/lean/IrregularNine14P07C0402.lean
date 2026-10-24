import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0131
import IrregularNine14P07C0132

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r24120 : Route 9 := (fun mask => (mask,id))

def c24120 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24120 : Upper (D 7) (R 7) [36,96,130,17,320,1] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,320,1] 13 (by decide) (choices 1) [2,8,128] r24120 c24120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7888
  · exact u7889
  · exact u7890

def b24121 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 25 336 34 201 137 393), lower := (rows 37 98 134 25 336 34 64 128 256), losses := [] }

theorem u24121 : Upper (D 7) (R 7) [36,96,130,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24122 : Route 9 := (fun mask => (mask,id))

def c24122 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24122 : Upper (D 7) (R 7) [36,96,130,17,320,8] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,320,8] 13 (by decide) (choices 1) [1,2,128] r24122 c24122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7891
  · exact u7892
  · exact u7893

def b24123 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 25 336 160 75 139 267), lower := (rows 37 98 134 25 336 160 64 128 256), losses := [] }

theorem u24123 : Upper (D 7) (R 7) [36,96,130,17,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24124 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 98, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 134 25 400 33 74 202 330), lower := (rows 37 98 134 25 400 33 64 128 256), losses := [] }

theorem u24124 : Upper (D 7) (R 7) [36,96,130,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24125 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 25 400 34 73 201 329), lower := (rows 37 98 134 25 400 34 64 128 256), losses := [] }

theorem u24125 : Upper (D 7) (R 7) [36,96,130,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24126 : Route 9 := (fun mask => (mask,id))

def c24126 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24126 : Upper (D 7) (R 7) [36,96,130,17,384,8] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,384,8] 13 (by decide) (choices 1) [1,2] r24126 c24126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7894
  · exact u7895

def b24127 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 25 400 96 75 139 267), lower := (rows 37 98 134 25 400 96 64 128 256), losses := [] }

theorem u24127 : Upper (D 7) (R 7) [36,96,130,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24128 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 388, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 98 134 26 81 33 456 392 392), lower := (rows 37 98 134 26 81 33 64 128 256), losses := [] }

theorem u24128 : Upper (D 7) (R 7) [36,96,130,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24129 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 134 26 81 40 449 385 385), lower := (rows 37 98 134 26 81 40 64 128 256), losses := [] }

theorem u24129 : Upper (D 7) (R 7) [36,96,130,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24129 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24130 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 26 81 160 329 393 265), lower := (rows 37 98 134 26 81 160 64 128 256), losses := [] }

theorem u24130 : Upper (D 7) (R 7) [36,96,130,18,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24131 : Route 9 := (fun mask => (mask,id))

def c24131 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24131 : Upper (D 7) (R 7) [36,96,130,18,65,256] 13 := by
  apply FastRouting.sound _ _ [36,96,130,18,65,256] 13 (by decide) (choices 1) [1,8,128] r24131 c24131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7896
  · exact u7897
  · exact u7898

def b24132 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(3,6),(4,6)], upper := (rows 37 98 134 26 145 33 328 456 328), lower := (rows 37 98 134 26 145 33 64 128 256), losses := [] }

theorem u24132 : Upper (D 7) (R 7) [36,96,130,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24133 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 37 98 134 26 145 40 321 449 321), lower := (rows 37 98 134 26 145 40 64 128 256), losses := [] }

theorem u24133 : Upper (D 7) (R 7) [36,96,130,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24133 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24134 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 26 145 96 329 393 265), lower := (rows 37 98 134 26 145 96 64 128 256), losses := [] }

theorem u24134 : Upper (D 7) (R 7) [36,96,130,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24135 : Route 9 := (fun mask => (mask,id))

def c24135 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24135 : Upper (D 7) (R 7) [36,96,130,18,129,256] 13 := by
  apply FastRouting.sound _ _ [36,96,130,18,129,256] 13 (by decide) (choices 1) [1,8] r24135 c24135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7899
  · exact u7900

def b24136 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 98 134 26 208 33 329 393 265), lower := (rows 37 98 134 26 208 33 64 128 256), losses := [] }

theorem u24136 : Upper (D 7) (R 7) [36,96,130,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24137 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 46, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 37 98 134 26 208 40 321 385 257), lower := (rows 37 98 134 26 208 40 64 128 256), losses := [] }

theorem u24137 : Upper (D 7) (R 7) [36,96,130,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24137 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24138 : Route 9 := (fun mask => (mask,id))

def c24138 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24138 : Upper (D 7) (R 7) [36,96,130,18,192,256] 13 := by
  apply FastRouting.sound _ _ [36,96,130,18,192,256] 13 (by decide) (choices 1) [1,8] r24138 c24138
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7901
  · exact u7902

def b24139 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 196, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 98 134 26 273 33 200 200 456), lower := (rows 37 98 134 26 273 33 64 128 256), losses := [] }

theorem u24139 : Upper (D 7) (R 7) [36,96,130,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24140 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 37 98 134 26 273 40 193 193 449), lower := (rows 37 98 134 26 273 40 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 17 0 81 145 273), good := (rows 469 66 134 478 465 12 64 128 256) }] }

theorem u24140 : Upper (D 7) (R 7) [36,96,130,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24140 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24141 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 26 273 96 201 137 393), lower := (rows 37 98 134 26 273 96 64 128 256), losses := [] }

theorem u24141 : Upper (D 7) (R 7) [36,96,130,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24142 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 26 273 160 73 201 329), lower := (rows 37 98 134 26 273 160 64 128 256), losses := [] }

theorem u24142 : Upper (D 7) (R 7) [36,96,130,18,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24143 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 98 134 26 280 33 193 193 449), lower := (rows 37 98 134 26 280 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 14 19 0 97 161 289), good := (rows 477 478 158 30 280 465 64 128 256) }] }

theorem u24143 : Upper (D 7) (R 7) [36,96,130,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24144 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 26 280 96 193 129 385), lower := (rows 37 98 134 26 280 96 64 128 256), losses := [] }

theorem u24144 : Upper (D 7) (R 7) [36,96,130,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24145 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 26 280 160 65 193 321), lower := (rows 37 98 134 26 280 160 64 128 256), losses := [] }

theorem u24145 : Upper (D 7) (R 7) [36,96,130,18,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24146 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 98 134 26 336 33 201 137 393), lower := (rows 37 98 134 26 336 33 64 128 256), losses := [] }

theorem u24146 : Upper (D 7) (R 7) [36,96,130,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24147 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 134 26 336 40 193 129 385), lower := (rows 37 98 134 26 336 40 64 128 256), losses := [] }

theorem u24147 : Upper (D 7) (R 7) [36,96,130,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24147 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24148 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 26 336 160 73 137 265), lower := (rows 37 98 134 26 336 160 64 128 256), losses := [] }

theorem u24148 : Upper (D 7) (R 7) [36,96,130,18,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24149 : Route 9 := (fun mask => (mask,id))

def c24149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24149 : Upper (D 7) (R 7) [36,96,130,18,384,1] 13 := by
  apply FastRouting.sound _ _ [36,96,130,18,384,1] 13 (by decide) (choices 1) [1,8] r24149 c24149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7903
  · exact u7904

def b24150 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7),(4,1),(4,5)], upper := (rows 37 98 134 26 400 40 65 193 321), lower := (rows 37 98 134 26 400 40 64 128 256), losses := [] }

theorem u24150 : Upper (D 7) (R 7) [36,96,130,18,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24150 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24151 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 134 26 400 96 73 137 265), lower := (rows 37 98 134 26 400 96 64 128 256), losses := [] }

theorem u24151 : Upper (D 7) (R 7) [36,96,130,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24152 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 73 145 34 344 408 280), lower := (rows 37 98 134 73 145 34 64 128 256), losses := [] }

theorem u24152 : Upper (D 7) (R 7) [36,96,130,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24153 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 134 73 145 40 338 402 274), lower := (rows 37 98 134 73 145 40 64 128 256), losses := [] }

theorem u24153 : Upper (D 7) (R 7) [36,96,130,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24153 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24154 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 37 98 134 73 145 48 330 394 266), lower := (rows 37 98 134 73 145 48 64 128 256), losses := [] }

theorem u24154 : Upper (D 7) (R 7) [36,96,130,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24154 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24155 : Route 9 := (fun mask => (mask,id))

def c24155 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24155 : Upper (D 7) (R 7) [36,96,130,65,129,256] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65,129,256] 13 (by decide) (choices 1) [2,8,16] r24155 c24155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7905
  · exact u7906
  · exact u7907

def b24156 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 34, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 134 73 152 33 338 402 274), lower := (rows 37 98 134 73 152 33 64 128 256), losses := [] }

theorem u24156 : Upper (D 7) (R 7) [36,96,130,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24157 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 73 152 34 337 401 273), lower := (rows 37 98 134 73 152 34 64 128 256), losses := [] }

theorem u24157 : Upper (D 7) (R 7) [36,96,130,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24158 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(1,7),(3,7)], upper := (rows 37 98 134 73 152 48 323 387 259), lower := (rows 37 98 134 73 152 48 64 128 256), losses := [] }

theorem u24158 : Upper (D 7) (R 7) [36,96,130,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24158 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24159 : Route 9 := (fun mask => (mask,id))

def c24159 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24159 : Upper (D 7) (R 7) [36,96,130,65,136,256] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65,136,256] 13 (by decide) (choices 1) [1,2,16] r24159 c24159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7908
  · exact u7909
  · exact u7910

def b24160 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 73 273 34 216 152 408), lower := (rows 37 98 134 73 273 34 64 128 256), losses := [] }

theorem u24160 : Upper (D 7) (R 7) [36,96,130,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24161 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 134 73 273 40 210 146 402), lower := (rows 37 98 134 73 273 40 64 128 256), losses := [] }

theorem u24161 : Upper (D 7) (R 7) [36,96,130,65,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24161 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24162 : Route 9 := (fun mask => (mask,id))

def c24162 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24162 : Upper (D 7) (R 7) [36,96,130,65,257,16] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65,257,16] 13 (by decide) (choices 1) [2,8,128] r24162 c24162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7911
  · exact u7912
  · exact u7913

def b24163 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 73 273 160 90 154 282), lower := (rows 37 98 134 73 273 160 64 128 256), losses := [] }

theorem u24163 : Upper (D 7) (R 7) [36,96,130,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24164 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 34, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 134 73 274 33 216 152 408), lower := (rows 37 98 134 73 274 33 64 128 256), losses := [] }

theorem u24164 : Upper (D 7) (R 7) [36,96,130,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24165 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 134 73 274 40 209 145 401), lower := (rows 37 98 134 73 274 40 64 128 256), losses := [] }

theorem u24165 : Upper (D 7) (R 7) [36,96,130,65,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24165 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24166 : Route 9 := (fun mask => (mask,id))

def c24166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24166 : Upper (D 7) (R 7) [36,96,130,65,258,16] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65,258,16] 13 (by decide) (choices 1) [1,8,128] r24166 c24166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7914
  · exact u7915
  · exact u7916

def b24167 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 73 274 160 89 153 281), lower := (rows 37 98 134 73 274 160 64 128 256), losses := [] }

theorem u24167 : Upper (D 7) (R 7) [36,96,130,65,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24168 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 34, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 134 73 280 33 210 146 402), lower := (rows 37 98 134 73 280 33 64 128 256), losses := [] }

theorem u24168 : Upper (D 7) (R 7) [36,96,130,65,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24169 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 73 280 34 209 145 401), lower := (rows 37 98 134 73 280 34 64 128 256), losses := [] }

theorem u24169 : Upper (D 7) (R 7) [36,96,130,65,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24170 : Route 9 := (fun mask => (mask,id))

def c24170 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24170 : Upper (D 7) (R 7) [36,96,130,65,264,16] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65,264,16] 13 (by decide) (choices 1) [1,2,128] r24170 c24170
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7917
  · exact u7918
  · exact u7919

def b24171 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 134 73 280 160 83 147 275), lower := (rows 37 98 134 73 280 160 64 128 256), losses := [] }

theorem u24171 : Upper (D 7) (R 7) [36,96,130,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24172 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 34, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 134 73 400 33 90 154 282), lower := (rows 37 98 134 73 400 33 64 128 256), losses := [] }

theorem u24172 : Upper (D 7) (R 7) [36,96,130,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24173 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 73 400 34 89 153 281), lower := (rows 37 98 134 73 400 34 64 128 256), losses := [] }

theorem u24173 : Upper (D 7) (R 7) [36,96,130,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24174 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 134 73 400 40 83 147 275), lower := (rows 37 98 134 73 400 40 64 128 256), losses := [] }

theorem u24174 : Upper (D 7) (R 7) [36,96,130,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24174 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24175 : Route 9 := (fun mask => (mask,id))

def c24175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24175 : Upper (D 7) (R 7) [36,96,130,65,384,16] 13 := by
  apply FastRouting.sound _ _ [36,96,130,65,384,16] 13 (by decide) (choices 1) [1,2,8] r24175 c24175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7920
  · exact u7921
  · exact u7922

def b24176 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 98 134 88 145 33 330 394 266), lower := (rows 37 98 134 88 145 33 64 128 256), losses := [] }

theorem u24176 : Upper (D 7) (R 7) [36,96,130,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24177 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 134 88 145 34 329 393 265), lower := (rows 37 98 134 88 145 34 64 128 256), losses := [] }

theorem u24177 : Upper (D 7) (R 7) [36,96,130,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24178 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 134 88 145 40 323 387 259), lower := (rows 37 98 134 88 145 40 64 128 256), losses := [] }

theorem u24178 : Upper (D 7) (R 7) [36,96,130,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24178 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24179 : Route 9 := (fun mask => (mask,id))

def c24179 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24179 : Upper (D 7) (R 7) [36,96,130,80,129,256] 13 := by
  apply FastRouting.sound _ _ [36,96,130,80,129,256] 13 (by decide) (choices 1) [1,2,8] r24179 c24179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7923
  · exact u7924
  · exact u7925

#print axioms u24179
end Delivery.IrregularNine14.P07
