import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0314
import IrregularNine14P06C0315

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r35160 : Route 9 := (fun mask => (mask,id))

def c35160 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35160 : Upper (D 6) (R 6) [24,36,192,5,257] 13 := by
  apply FastRouting.sound _ _ [24,36,192,5,257] 13 (by decide) (choices 1) [2,64] r35160 c35160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18866
  · exact u18867

def r35161 : Route 9 := (fun mask => (mask,id))

def c35161 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35161 : Upper (D 6) (R 6) [24,36,192,5,258] 13 := by
  apply FastRouting.sound _ _ [24,36,192,5,258] 13 (by decide) (choices 1) [1,2,64] r35161 c35161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18868
  · exact u18869
  · exact u18870

def r35162 : Route 9 := (fun mask => (mask,id))

def c35162 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35162 : Upper (D 6) (R 6) [24,36,192,5,288] 13 := by
  apply FastRouting.sound _ _ [24,36,192,5,288] 13 (by decide) (choices 1) [1,2,64] r35162 c35162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18871
  · exact u18872
  · exact u18873

def r35163 : Route 9 := (fun mask => (mask,id))

def c35163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35163 : Upper (D 6) (R 6) [24,36,192,5,320] 13 := by
  apply FastRouting.sound _ _ [24,36,192,5,320] 13 (by decide) (choices 1) [1,2] r35163 c35163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18874
  · exact u18875

def b35164 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 196 14 49 355 323 451 323), lower := (rows 25 38 196 14 49 32 64 128 256), losses := [] }

theorem u35164 : Upper (D 6) (R 6) [24,36,192,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35165 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 196 14 81 291 355 419 291), lower := (rows 25 38 196 14 81 32 64 128 256), losses := [] }

theorem u35165 : Upper (D 6) (R 6) [24,36,192,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35166 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 196 14 82 289 353 417 289), lower := (rows 25 38 196 14 82 32 64 128 256), losses := [] }

theorem u35166 : Upper (D 6) (R 6) [24,36,192,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35167 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 196 14 112 291 323 387 259), lower := (rows 25 38 196 14 112 32 64 128 256), losses := [] }

theorem u35167 : Upper (D 6) (R 6) [24,36,192,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35168 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 196 14 273 99 99 227 355), lower := (rows 25 38 196 14 273 32 64 128 256), losses := [] }

theorem u35168 : Upper (D 6) (R 6) [24,36,192,6,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35169 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 196 14 274 97 97 225 353), lower := (rows 25 38 196 14 274 32 64 128 256), losses := [] }

theorem u35169 : Upper (D 6) (R 6) [24,36,192,6,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35170 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 196 14 304 99 67 195 323), lower := (rows 25 38 196 14 304 32 64 128 256), losses := [] }

theorem u35170 : Upper (D 6) (R 6) [24,36,192,6,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35171 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 196 14 336 35 99 163 291), lower := (rows 25 38 196 14 336 32 64 128 256), losses := [] }

theorem u35171 : Upper (D 6) (R 6) [24,36,192,6,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35172 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 38 196 41 81 294 326 390 262), lower := (rows 25 38 196 41 81 32 64 128 256), losses := [] }

theorem u35172 : Upper (D 6) (R 6) [24,36,192,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35173 : Route 9 := (fun mask => (mask,id))

def c35173 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35173 : Upper (D 6) (R 6) [24,36,192,33,66] 13 := by
  apply FastRouting.sound _ _ [24,36,192,33,66] 13 (by decide) (choices 1) [1,2,4,256] r35173 c35173
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18876
  · exact u18877
  · exact u18878
  · exact u18879

def b35174 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 25 38 196 41 84 291 323 387 259), lower := (rows 25 38 196 41 84 32 64 128 256), losses := [] }

theorem u35174 : Upper (D 6) (R 6) [24,36,192,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35175 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 38 196 41 273 102 70 198 326), lower := (rows 25 38 196 41 273 32 64 128 256), losses := [] }

theorem u35175 : Upper (D 6) (R 6) [24,36,192,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35176 : Route 9 := (fun mask => (mask,id))

def c35176 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35176 : Upper (D 6) (R 6) [24,36,192,33,258] 13 := by
  apply FastRouting.sound _ _ [24,36,192,33,258] 13 (by decide) (choices 1) [1,2,4,64] r35176 c35176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18880
  · exact u18881
  · exact u18882
  · exact u18883

def r35177 : Route 9 := (fun mask => (mask,id))

def c35177 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35177 : Upper (D 6) (R 6) [24,36,192,33,260] 13 := by
  apply FastRouting.sound _ _ [24,36,192,33,260] 13 (by decide) (choices 1) [1,2,64] r35177 c35177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18884
  · exact u18885
  · exact u18886

def r35178 : Route 9 := (fun mask => (mask,id))

def c35178 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35178 : Upper (D 6) (R 6) [24,36,192,33,320] 13 := by
  apply FastRouting.sound _ _ [24,36,192,33,320] 13 (by decide) (choices 1) [1,2,4] r35178 c35178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18887
  · exact u18888
  · exact u18889

def b35179 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 196 42 81 295 327 391 263), lower := (rows 25 38 196 42 81 32 64 128 256), losses := [] }

theorem u35179 : Upper (D 6) (R 6) [24,36,192,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35180 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 196 42 82 293 325 389 261), lower := (rows 25 38 196 42 82 32 64 128 256), losses := [] }

theorem u35180 : Upper (D 6) (R 6) [24,36,192,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35181 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 196 42 273 103 71 199 327), lower := (rows 25 38 196 42 273 32 64 128 256), losses := [] }

theorem u35181 : Upper (D 6) (R 6) [24,36,192,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35182 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 196 42 274 101 69 197 325), lower := (rows 25 38 196 42 274 32 64 128 256), losses := [] }

theorem u35182 : Upper (D 6) (R 6) [24,36,192,34,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35183 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 196 42 276 99 67 195 323), lower := (rows 25 38 196 42 276 32 64 128 256), losses := [] }

theorem u35183 : Upper (D 6) (R 6) [24,36,192,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35184 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 196 42 336 39 71 135 263), lower := (rows 25 38 196 42 336 32 64 128 256), losses := [] }

theorem u35184 : Upper (D 6) (R 6) [24,36,192,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35185 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 196 44 81 291 323 387 259), lower := (rows 25 38 196 44 81 32 64 128 256), losses := [] }

theorem u35185 : Upper (D 6) (R 6) [24,36,192,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35186 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 196 44 82 291 323 387 259), lower := (rows 25 38 196 44 82 32 64 128 256), losses := [] }

theorem u35186 : Upper (D 6) (R 6) [24,36,192,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35187 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 196 44 273 99 67 195 323), lower := (rows 25 38 196 44 273 32 64 128 256), losses := [] }

theorem u35187 : Upper (D 6) (R 6) [24,36,192,36,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35188 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 196 44 274 99 67 195 323), lower := (rows 25 38 196 44 274 32 64 128 256), losses := [] }

theorem u35188 : Upper (D 6) (R 6) [24,36,192,36,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35189 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 196 44 336 35 67 131 259), lower := (rows 25 38 196 44 336 32 64 128 256), losses := [] }

theorem u35189 : Upper (D 6) (R 6) [24,36,192,36,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35190 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 196 73 273 38 102 166 294), lower := (rows 25 38 196 73 273 32 64 128 256), losses := [] }

theorem u35190 : Upper (D 6) (R 6) [24,36,192,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35191 : Route 9 := (fun mask => (mask,id))

def c35191 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35191 : Upper (D 6) (R 6) [24,36,192,65,258] 13 := by
  apply FastRouting.sound _ _ [24,36,192,65,258] 13 (by decide) (choices 1) [1,2,4] r35191 c35191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18890
  · exact u18891
  · exact u18892

def r35192 : Route 9 := (fun mask => (mask,id))

def c35192 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35192 : Upper (D 6) (R 6) [24,36,192,65,260] 13 := by
  apply FastRouting.sound _ _ [24,36,192,65,260] 13 (by decide) (choices 1) [1,2] r35192 c35192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18893
  · exact u18894

def r35193 : Route 9 := (fun mask => (mask,id))

def c35193 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35193 : Upper (D 6) (R 6) [24,36,192,65,288] 13 := by
  apply FastRouting.sound _ _ [24,36,192,65,288] 13 (by decide) (choices 1) [1,2,4] r35193 c35193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18895
  · exact u18896
  · exact u18897

def r35194 : Route 9 := (fun mask => (mask,id))

def c35194 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35194 : Upper (D 6) (R 6) [24,36,192,66,257] 13 := by
  apply FastRouting.sound _ _ [24,36,192,66,257] 13 (by decide) (choices 1) [1,2,4] r35194 c35194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18898
  · exact u18899
  · exact u18900

def r35195 : Route 9 := (fun mask => (mask,id))

def c35195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35195 : Upper (D 6) (R 6) [24,36,192,66,258] 13 := by
  apply FastRouting.sound _ _ [24,36,192,66,258] 13 (by decide) (choices 1) [1,4] r35195 c35195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18901
  · exact u18902

def r35196 : Route 9 := (fun mask => (mask,id))

def c35196 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35196 : Upper (D 6) (R 6) [24,36,192,66,260] 13 := by
  apply FastRouting.sound _ _ [24,36,192,66,260] 13 (by decide) (choices 1) [1,2] r35196 c35196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18903
  · exact u18904

def r35197 : Route 9 := (fun mask => (mask,id))

def c35197 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35197 : Upper (D 6) (R 6) [24,36,192,66,288] 13 := by
  apply FastRouting.sound _ _ [24,36,192,66,288] 13 (by decide) (choices 1) [1,2,4] r35197 c35197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18905
  · exact u18906
  · exact u18907

def b35198 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 38 196 76 273 35 99 163 291), lower := (rows 25 38 196 76 273 32 64 128 256), losses := [] }

theorem u35198 : Upper (D 6) (R 6) [24,36,192,68,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35199 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 38 196 76 274 35 99 163 291), lower := (rows 25 38 196 76 274 32 64 128 256), losses := [] }

theorem u35199 : Upper (D 6) (R 6) [24,36,192,68,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35200 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 25 38 196 76 304 35 67 131 259), lower := (rows 25 38 196 76 304 32 64 128 256), losses := [] }

theorem u35200 : Upper (D 6) (R 6) [24,36,192,68,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35201 : Route 9 := (fun mask => (mask,id))

def c35201 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35201 : Upper (D 6) (R 6) [24,36,192,96,257] 13 := by
  apply FastRouting.sound _ _ [24,36,192,96,257] 13 (by decide) (choices 1) [1,2,4] r35201 c35201
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18908
  · exact u18909
  · exact u18910

def r35202 : Route 9 := (fun mask => (mask,id))

def c35202 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35202 : Upper (D 6) (R 6) [24,36,192,96,258] 13 := by
  apply FastRouting.sound _ _ [24,36,192,96,258] 13 (by decide) (choices 1) [1,2,4] r35202 c35202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18911
  · exact u18912
  · exact u18913

def r35203 : Route 9 := (fun mask => (mask,id))

def c35203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35203 : Upper (D 6) (R 6) [24,36,192,96,260] 13 := by
  apply FastRouting.sound _ _ [24,36,192,96,260] 13 (by decide) (choices 1) [1,2] r35203 c35203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18914
  · exact u18915

def b35204 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 38 388 11 19 100 100 228 356), lower := (rows 25 38 388 11 19 32 64 128 256), losses := [] }

theorem u35204 : Upper (D 6) (R 6) [24,36,384,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35205 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 38 388 11 21 98 98 226 354), lower := (rows 25 38 388 11 21 32 64 128 256), losses := [] }

theorem u35205 : Upper (D 6) (R 6) [24,36,384,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35206 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 38 388 11 22 97 97 225 353), lower := (rows 25 38 388 11 22 32 64 128 256), losses := [] }

theorem u35206 : Upper (D 6) (R 6) [24,36,384,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35207 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 38 388 11 49 102 70 198 326), lower := (rows 25 38 388 11 49 32 64 128 256), losses := [] }

theorem u35207 : Upper (D 6) (R 6) [24,36,384,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35208 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 38 388 11 50 101 69 197 325), lower := (rows 25 38 388 11 50 32 64 128 256), losses := [] }

theorem u35208 : Upper (D 6) (R 6) [24,36,384,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35209 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 388 11 52 99 67 195 323), lower := (rows 25 38 388 11 52 32 64 128 256), losses := [] }

theorem u35209 : Upper (D 6) (R 6) [24,36,384,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35210 : Route 9 := (fun mask => (mask,id))

def c35210 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35210 : Upper (D 6) (R 6) [24,36,384,3,65] 13 := by
  apply FastRouting.sound _ _ [24,36,384,3,65] 13 (by decide) (choices 1) [2,4,64] r35210 c35210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18916
  · exact u18917
  · exact u18918

def b35211 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 38 388 11 82 101 101 229 357), lower := (rows 25 38 388 11 82 32 64 128 256), losses := [] }

theorem u35211 : Upper (D 6) (R 6) [24,36,384,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35212 : Route 9 := (fun mask => (mask,id))

def c35212 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35212 : Upper (D 6) (R 6) [24,36,384,3,68] 13 := by
  apply FastRouting.sound _ _ [24,36,384,3,68] 13 (by decide) (choices 1) [1,2,64] r35212 c35212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18919
  · exact u18920
  · exact u18921

def r35213 : Route 9 := (fun mask => (mask,id))

def c35213 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35213 : Upper (D 6) (R 6) [24,36,384,3,96] 13 := by
  apply FastRouting.sound _ _ [24,36,384,3,96] 13 (by decide) (choices 1) [1,2,4,64] r35213 c35213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18922
  · exact u18923
  · exact u18924
  · exact u18925

def b35214 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 25, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 388 13 49 98 66 194 322), lower := (rows 25 38 388 13 49 32 64 128 256), losses := [] }

theorem u35214 : Upper (D 6) (R 6) [24,36,384,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35215 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 388 13 50 99 67 195 323), lower := (rows 25 38 388 13 50 32 64 128 256), losses := [] }

theorem u35215 : Upper (D 6) (R 6) [24,36,384,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35216 : Route 9 := (fun mask => (mask,id))

def c35216 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35216 : Upper (D 6) (R 6) [24,36,384,5,65] 13 := by
  apply FastRouting.sound _ _ [24,36,384,5,65] 13 (by decide) (choices 1) [2,64] r35216 c35216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18926
  · exact u18927

def r35217 : Route 9 := (fun mask => (mask,id))

def c35217 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35217 : Upper (D 6) (R 6) [24,36,384,5,66] 13 := by
  apply FastRouting.sound _ _ [24,36,384,5,66] 13 (by decide) (choices 1) [1,2,64] r35217 c35217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18928
  · exact u18929
  · exact u18930

def r35218 : Route 9 := (fun mask => (mask,id))

def c35218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35218 : Upper (D 6) (R 6) [24,36,384,5,96] 13 := by
  apply FastRouting.sound _ _ [24,36,384,5,96] 13 (by decide) (choices 1) [1,2,64] r35218 c35218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18931
  · exact u18932
  · exact u18933

def b35219 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 388 14 49 99 67 195 323), lower := (rows 25 38 388 14 49 32 64 128 256), losses := [] }

theorem u35219 : Upper (D 6) (R 6) [24,36,384,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u35219
end Delivery.IrregularNine14.P06
