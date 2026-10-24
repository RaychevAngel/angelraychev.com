import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0111

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22140 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 418, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(3,7)], upper := (rows 37 42 22 73 145 160 322 450 322), lower := (rows 37 42 22 73 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 40 53 73 177 160 64 160 256) }] }

theorem u22140 : Upper (D 7) (R 7) [36,40,18,65,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22141 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 37 42 22 73 145 288 194 194 450), lower := (rows 37 42 22 73 145 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 17 0 70 134 262), good := (rows 477 458 470 89 153 256 64 128 256) }] }

theorem u22141 : Upper (D 7) (R 7) [36,40,18,65,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22141 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22142 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 42 22 73 208 33 450 386 386), lower := (rows 37 42 22 73 208 33 64 128 256), losses := [] }

theorem u22142 : Upper (D 7) (R 7) [36,40,18,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22143 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 73 208 34 449 385 385), lower := (rows 37 42 22 73 208 34 64 128 256), losses := [] }

theorem u22143 : Upper (D 7) (R 7) [36,40,18,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22144 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 417, targets := 64 },{ cop := 3, region := 418, targets := 64 }], pairs := [(0,6),(1,6),(1,7),(3,7)], upper := (rows 37 42 22 73 208 160 323 387 259), lower := (rows 37 42 22 73 208 160 64 128 256), losses := [] }

theorem u22144 : Upper (D 7) (R 7) [36,40,18,65,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22145 : Route 9 := (fun mask => (mask,id))

def c22145 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22145 : Upper (D 7) (R 7) [36,40,18,65,192,256] 13 := by
  apply FastRouting.sound _ _ [36,40,18,65,192,256] 13 (by decide) (choices 1) [1,2,128] r22145 c22145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6677
  · exact u6678
  · exact u6679

def b22146 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 73 273 34 192 192 448), lower := (rows 37 42 22 73 273 34 64 128 256), losses := [] }

theorem u22146 : Upper (D 7) (R 7) [36,40,18,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22147 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 42 22 73 273 96 194 130 386), lower := (rows 37 42 22 73 273 96 64 128 256), losses := [] }

theorem u22147 : Upper (D 7) (R 7) [36,40,18,65,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22148 : Route 9 := (fun mask => (mask,id))

def c22148 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22148 : Upper (D 7) (R 7) [36,40,18,65,257,128] 13 := by
  apply FastRouting.sound _ _ [36,40,18,65,257,128] 13 (by decide) (choices 1) [2,128] r22148 c22148
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6680
  · exact u6681

def b22149 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 42 22 73 336 33 194 130 386), lower := (rows 37 42 22 73 336 33 64 128 256), losses := [] }

theorem u22149 : Upper (D 7) (R 7) [36,40,18,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22150 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 73 336 34 193 129 385), lower := (rows 37 42 22 73 336 34 64 128 256), losses := [] }

theorem u22150 : Upper (D 7) (R 7) [36,40,18,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22151 : Route 9 := (fun mask => (mask,id))

def c22151 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22151 : Upper (D 7) (R 7) [36,40,18,65,320,128] 13 := by
  apply FastRouting.sound _ _ [36,40,18,65,320,128] 13 (by decide) (choices 1) [1,2,128] r22151 c22151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6682
  · exact u6683
  · exact u6684

def b22152 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 42 22 73 400 33 194 194 450), lower := (rows 37 42 22 73 400 33 64 128 256), losses := [] }

theorem u22152 : Upper (D 7) (R 7) [36,40,18,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22153 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 73 400 34 193 193 449), lower := (rows 37 42 22 73 400 34 64 128 256), losses := [] }

theorem u22153 : Upper (D 7) (R 7) [36,40,18,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22153 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22154 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 42 22 73 400 96 195 131 387), lower := (rows 37 42 22 73 400 96 64 128 256), losses := [] }

theorem u22154 : Upper (D 7) (R 7) [36,40,18,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22155 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 74, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 42 22 73 400 160 67 195 323), lower := (rows 37 42 22 73 400 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 40 53 73 432 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 42 55 9 432 160 0 160 256) }] }

theorem u22155 : Upper (D 7) (R 7) [36,40,18,65,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22155 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22156 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 497, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 42 22 74 400 33 193 193 449), lower := (rows 37 42 22 74 400 33 64 128 256), losses := [] }

theorem u22156 : Upper (D 7) (R 7) [36,40,18,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22156 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22157 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 10, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 42 22 74 400 96 193 129 385), lower := (rows 37 42 22 74 400 96 64 128 256), losses := [] }

theorem u22157 : Upper (D 7) (R 7) [36,40,18,66,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22157 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22158 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 2, region := 497, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,1)], upper := (rows 37 42 22 74 400 160 65 193 321), lower := (rows 37 42 22 74 400 160 64 128 256), losses := [] }

theorem u22158 : Upper (D 7) (R 7) [36,40,18,66,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22158 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22159 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 42 22 200 81 33 450 386 386), lower := (rows 37 42 22 200 81 33 64 128 256), losses := [] }

theorem u22159 : Upper (D 7) (R 7) [36,40,18,192,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22160 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 200 81 34 449 385 385), lower := (rows 37 42 22 200 81 34 64 128 256), losses := [] }

theorem u22160 : Upper (D 7) (R 7) [36,40,18,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22161 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 22 200 81 160 323 387 259), lower := (rows 37 42 22 200 81 160 64 128 256), losses := [] }

theorem u22161 : Upper (D 7) (R 7) [36,40,18,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22162 : Route 9 := (fun mask => (mask,id))

def c22162 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22162 : Upper (D 7) (R 7) [36,40,18,192,65,256] 13 := by
  apply FastRouting.sound _ _ [36,40,18,192,65,256] 13 (by decide) (choices 1) [1,2,128] r22162 c22162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6685
  · exact u6686
  · exact u6687

def b22163 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 202, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 42 22 200 273 33 194 194 450), lower := (rows 37 42 22 200 273 33 64 128 256), losses := [] }

theorem u22163 : Upper (D 7) (R 7) [36,40,18,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22163 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22164 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 200 273 34 193 193 449), lower := (rows 37 42 22 200 273 34 64 128 256), losses := [] }

theorem u22164 : Upper (D 7) (R 7) [36,40,18,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22165 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 42 22 200 273 96 195 131 387), lower := (rows 37 42 22 200 273 96 64 128 256), losses := [] }

theorem u22165 : Upper (D 7) (R 7) [36,40,18,192,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22165 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22166 : Route 9 := (fun mask => (mask,id))

def c22166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22166 : Upper (D 7) (R 7) [36,40,18,192,320,1] 13 := by
  apply FastRouting.sound _ _ [36,40,18,192,320,1] 13 (by decide) (choices 1) [1,2,128] r22166 c22166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6688
  · exact u6689
  · exact u6690

def b22167 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 200 336 34 193 129 385), lower := (rows 37 42 22 200 336 34 64 128 256), losses := [] }

theorem u22167 : Upper (D 7) (R 7) [36,40,18,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22168 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 22 200 336 160 67 131 259), lower := (rows 37 42 22 200 336 160 64 128 256), losses := [] }

theorem u22168 : Upper (D 7) (R 7) [36,40,18,192,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22169 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 265 81 34 192 192 448), lower := (rows 37 42 22 265 81 34 64 128 256), losses := [] }

theorem u22169 : Upper (D 7) (R 7) [36,40,18,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22170 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,1),(1,0),(1,6),(3,6)], upper := (rows 37 42 22 265 81 96 194 130 386), lower := (rows 37 42 22 265 81 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 112 64 128 256), good := (rows 37 40 53 265 113 96 96 128 256) }] }

theorem u22170 : Upper (D 7) (R 7) [36,40,18,257,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22171 : Route 9 := (fun mask => (mask,id))

def c22171 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22171 : Upper (D 7) (R 7) [36,40,18,257,65,128] 13 := by
  apply FastRouting.sound _ _ [36,40,18,257,65,128] 13 (by decide) (choices 1) [2,128] r22171 c22171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6691
  · exact u6692

def b22172 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 42 22 265 208 33 194 194 450), lower := (rows 37 42 22 265 208 33 64 128 256), losses := [] }

theorem u22172 : Upper (D 7) (R 7) [36,40,18,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22173 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 265 208 34 193 193 449), lower := (rows 37 42 22 265 208 34 64 128 256), losses := [] }

theorem u22173 : Upper (D 7) (R 7) [36,40,18,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22174 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(0,1),(0,7),(1,6),(3,6)], upper := (rows 37 42 22 265 208 96 195 131 387), lower := (rows 37 42 22 265 208 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 112 64 128 256), good := (rows 37 40 53 265 240 96 96 128 256) },{ target := 7, region := (rows 5 2 4 8 16 112 64 0 256), good := (rows 37 42 55 265 112 96 96 0 256) }] }

theorem u22174 : Upper (D 7) (R 7) [36,40,18,257,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22175 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 241, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,1),(0,6),(0,7),(4,1)], upper := (rows 37 42 22 266 208 33 193 193 449), lower := (rows 37 42 22 266 208 33 64 128 256), losses := [] }

theorem u22175 : Upper (D 7) (R 7) [36,40,18,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22176 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 394, targets := 64 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,1)], upper := (rows 37 42 22 266 208 96 193 129 385), lower := (rows 37 42 22 266 208 96 64 128 256), losses := [] }

theorem u22176 : Upper (D 7) (R 7) [36,40,18,258,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22177 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 42 22 328 81 33 194 130 386), lower := (rows 37 42 22 328 81 33 64 128 256), losses := [] }

theorem u22177 : Upper (D 7) (R 7) [36,40,18,320,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22178 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 328 81 34 193 129 385), lower := (rows 37 42 22 328 81 34 64 128 256), losses := [] }

theorem u22178 : Upper (D 7) (R 7) [36,40,18,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22179 : Route 9 := (fun mask => (mask,id))

def c22179 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22179 : Upper (D 7) (R 7) [36,40,18,320,65,128] 13 := by
  apply FastRouting.sound _ _ [36,40,18,320,65,128] 13 (by decide) (choices 1) [1,2,128] r22179 c22179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6693
  · exact u6694
  · exact u6695

def b22180 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 42 22 328 145 33 194 194 450), lower := (rows 37 42 22 328 145 33 64 128 256), losses := [] }

theorem u22180 : Upper (D 7) (R 7) [36,40,18,320,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22181 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 328 145 34 193 193 449), lower := (rows 37 42 22 328 145 34 64 128 256), losses := [] }

theorem u22181 : Upper (D 7) (R 7) [36,40,18,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22182 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 149, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,6)], upper := (rows 37 42 22 328 145 96 195 131 387), lower := (rows 37 42 22 328 145 96 64 128 256), losses := [] }

theorem u22182 : Upper (D 7) (R 7) [36,40,18,320,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22182 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22183 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 42 22 328 145 160 67 195 323), lower := (rows 37 42 22 328 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 40 53 328 177 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 176 0 128 256), good := (rows 37 42 55 264 177 160 0 160 256) }] }

theorem u22183 : Upper (D 7) (R 7) [36,40,18,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22183 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22184 : Route 9 := (fun mask => (mask,id))

def c22184 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22184 : Upper (D 7) (R 7) [36,40,18,320,192,1] 13 := by
  apply FastRouting.sound _ _ [36,40,18,320,192,1] 13 (by decide) (choices 1) [1,2,128] r22184 c22184
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6696
  · exact u6697
  · exact u6698

def b22185 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 42 22 328 208 34 193 129 385), lower := (rows 37 42 22 328 208 34 64 128 256), losses := [] }

theorem u22185 : Upper (D 7) (R 7) [36,40,18,320,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22185 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22186 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(1,7),(3,7)], upper := (rows 37 42 22 328 208 160 67 131 259), lower := (rows 37 42 22 328 208 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 40 53 328 240 160 64 160 256) }] }

theorem u22186 : Upper (D 7) (R 7) [36,40,18,320,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22187 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 42 69 88 145 34 450 386 386), lower := (rows 37 42 69 88 145 34 64 128 256), losses := [] }

theorem u22187 : Upper (D 7) (R 7) [36,40,65,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22188 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 325, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 42 69 88 145 160 322 386 258), lower := (rows 37 42 69 88 145 160 64 128 256), losses := [] }

theorem u22188 : Upper (D 7) (R 7) [36,40,65,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22188 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22189 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 37 42 69 88 145 288 194 130 386), lower := (rows 37 42 69 88 145 288 64 128 256), losses := [] }

theorem u22189 : Upper (D 7) (R 7) [36,40,65,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22189 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22190 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 88 146 33 450 386 386), lower := (rows 37 42 69 88 146 33 64 128 256), losses := [] }

theorem u22190 : Upper (D 7) (R 7) [36,40,65,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22191 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 452, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(2,7)], upper := (rows 37 42 69 88 146 34 449 385 385), lower := (rows 37 42 69 88 146 34 64 128 256), losses := [] }

theorem u22191 : Upper (D 7) (R 7) [36,40,65,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22192 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(2,7)], upper := (rows 37 42 69 88 146 160 323 387 259), lower := (rows 37 42 69 88 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 36 42 68 122 178 160 64 160 256) },{ target := 1, region := (rows 11 0 12 8 16 176 64 128 256), good := (rows 37 45 69 125 177 160 64 160 256) }] }

theorem u22192 : Upper (D 7) (R 7) [36,40,65,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22192 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22193 : Route 9 := (fun mask => (mask,id))

def c22193 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22193 : Upper (D 7) (R 7) [36,40,65,80,130,256] 13 := by
  apply FastRouting.sound _ _ [36,40,65,80,130,256] 13 (by decide) (choices 1) [1,2,128] r22193 c22193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6699
  · exact u6700
  · exact u6701

def b22194 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 42 69 88 273 34 194 130 386), lower := (rows 37 42 69 88 273 34 64 128 256), losses := [] }

theorem u22194 : Upper (D 7) (R 7) [36,40,65,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22195 : Route 9 := (fun mask => (mask,id))

def c22195 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22195 : Upper (D 7) (R 7) [36,40,65,80,257,128] 13 := by
  apply FastRouting.sound _ _ [36,40,65,80,257,128] 13 (by decide) (choices 1) [2,128] r22195 c22195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6702
  · exact u6703

def b22196 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 88 274 33 194 130 386), lower := (rows 37 42 69 88 274 33 64 128 256), losses := [] }

theorem u22196 : Upper (D 7) (R 7) [36,40,65,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22196 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22197 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(2,7)], upper := (rows 37 42 69 88 274 34 193 129 385), lower := (rows 37 42 69 88 274 34 64 128 256), losses := [] }

theorem u22197 : Upper (D 7) (R 7) [36,40,65,80,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22198 : Route 9 := (fun mask => (mask,id))

def c22198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22198 : Upper (D 7) (R 7) [36,40,65,80,258,128] 13 := by
  apply FastRouting.sound _ _ [36,40,65,80,258,128] 13 (by decide) (choices 1) [1,2,128] r22198 c22198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6704
  · exact u6705
  · exact u6706

def b22199 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 88 400 33 194 130 386), lower := (rows 37 42 69 88 400 33 64 128 256), losses := [] }

theorem u22199 : Upper (D 7) (R 7) [36,40,65,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22199 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22199
end Delivery.IrregularNine14.P07
