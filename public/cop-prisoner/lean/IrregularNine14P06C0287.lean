import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0076

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17220 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 76 273 34 69 197 325), lower := (rows 11 162 52 76 273 34 64 128 256), losses := [] }

theorem u17220 : Upper (D 6) (R 6) [10,160,48,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17221 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 52 76 273 36 67 195 323), lower := (rows 11 162 52 76 273 36 64 128 256), losses := [] }

theorem u17221 : Upper (D 6) (R 6) [10,160,48,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17222 : Route 9 := (fun mask => (mask,id))

def c17222 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17222 : Upper (D 6) (R 6) [10,160,48,68,257,64] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,257,64] 13 (by decide) (choices 1) [1,2,4] r17222 c17222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4565
  · exact u4566
  · exact u4567

def r17223 : Route 9 := (fun mask => (mask,id))

def c17223 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17223 : Upper (D 6) (R 6) [10,160,48,68,258,1] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,258,1] 13 (by decide) (choices 1) [1,4] r17223 c17223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4568
  · exact u4569

def b17224 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 52 76 274 36 65 193 321), lower := (rows 11 162 52 76 274 36 64 128 256), losses := [] }

theorem u17224 : Upper (D 6) (R 6) [10,160,48,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17225 : Route 9 := (fun mask => (mask,id))

def c17225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17225 : Upper (D 6) (R 6) [10,160,48,68,258,64] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,258,64] 13 (by decide) (choices 1) [1,4] r17225 c17225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4570
  · exact u4571

def r17226 : Route 9 := (fun mask => (mask,id))

def c17226 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17226 : Upper (D 6) (R 6) [10,160,48,68,260,1] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,260,1] 13 (by decide) (choices 1) [1,2] r17226 c17226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4572
  · exact u4573

def b17227 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 76 276 34 65 193 321), lower := (rows 11 162 52 76 276 34 64 128 256), losses := [] }

theorem u17227 : Upper (D 6) (R 6) [10,160,48,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17228 : Route 9 := (fun mask => (mask,id))

def c17228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17228 : Upper (D 6) (R 6) [10,160,48,68,260,64] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,260,64] 13 (by decide) (choices 1) [1,2] r17228 c17228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4574
  · exact u4575

def r17229 : Route 9 := (fun mask => (mask,id))

def c17229 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17229 : Upper (D 6) (R 6) [10,160,48,68,320,1] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,320,1] 13 (by decide) (choices 1) [1,2,4] r17229 c17229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4576
  · exact u4577
  · exact u4578

def b17230 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 76 336 34 69 133 261), lower := (rows 11 162 52 76 336 34 64 128 256), losses := [] }

theorem u17230 : Upper (D 6) (R 6) [10,160,48,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17231 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 162 52 76 336 36 67 131 259), lower := (rows 11 162 52 76 336 36 64 128 256), losses := [] }

theorem u17231 : Upper (D 6) (R 6) [10,160,48,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17232 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 265 21 34 68 196 324), lower := (rows 11 162 52 265 21 34 64 128 256), losses := [] }

theorem u17232 : Upper (D 6) (R 6) [10,160,48,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17233 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 162 52 265 21 36 66 194 322), lower := (rows 11 162 52 265 21 36 64 128 256), losses := [] }

theorem u17233 : Upper (D 6) (R 6) [10,160,48,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17234 : Route 9 := (fun mask => (mask,id))

def c17234 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17234 : Upper (D 6) (R 6) [10,160,48,257,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,48,257,5,64] 13 (by decide) (choices 1) [2,4] r17234 c17234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4579
  · exact u4580

def b17235 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 265 81 34 68 196 324), lower := (rows 11 162 52 265 81 34 64 128 256), losses := [] }

theorem u17235 : Upper (D 6) (R 6) [10,160,48,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17236 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 52 265 81 36 70 198 326), lower := (rows 11 162 52 265 81 36 64 128 256), losses := [] }

theorem u17236 : Upper (D 6) (R 6) [10,160,48,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17237 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 52 265 81 96 70 134 262), lower := (rows 11 162 52 265 81 96 64 128 256), losses := [] }

theorem u17237 : Upper (D 6) (R 6) [10,160,48,257,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17238 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 52 265 82 33 68 196 324), lower := (rows 11 162 52 265 82 33 64 128 256), losses := [] }

theorem u17238 : Upper (D 6) (R 6) [10,160,48,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17239 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 52 265 82 36 69 197 325), lower := (rows 11 162 52 265 82 36 64 128 256), losses := [] }

theorem u17239 : Upper (D 6) (R 6) [10,160,48,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17240 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 52 265 82 96 69 133 261), lower := (rows 11 162 52 265 82 96 64 128 256), losses := [] }

theorem u17240 : Upper (D 6) (R 6) [10,160,48,257,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17241 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 52 265 84 33 70 198 326), lower := (rows 11 162 52 265 84 33 64 128 256), losses := [] }

theorem u17241 : Upper (D 6) (R 6) [10,160,48,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17242 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 265 84 34 69 197 325), lower := (rows 11 162 52 265 84 34 64 128 256), losses := [] }

theorem u17242 : Upper (D 6) (R 6) [10,160,48,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17243 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 52 265 84 36 67 195 323), lower := (rows 11 162 52 265 84 36 64 128 256), losses := [] }

theorem u17243 : Upper (D 6) (R 6) [10,160,48,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17244 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 52 265 84 96 71 135 263), lower := (rows 11 162 52 265 84 96 64 128 256), losses := [] }

theorem u17244 : Upper (D 6) (R 6) [10,160,48,257,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17245 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 458, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 11 162 52 268 81 33 70 198 326), lower := (rows 11 162 52 268 81 33 64 128 256), losses := [] }

theorem u17245 : Upper (D 6) (R 6) [10,160,48,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17246 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 268 81 34 69 197 325), lower := (rows 11 162 52 268 81 34 64 128 256), losses := [] }

theorem u17246 : Upper (D 6) (R 6) [10,160,48,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17247 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 52 268 81 36 67 195 323), lower := (rows 11 162 52 268 81 36 64 128 256), losses := [] }

theorem u17247 : Upper (D 6) (R 6) [10,160,48,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17248 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 52 268 81 96 71 135 263), lower := (rows 11 162 52 268 81 96 64 128 256), losses := [] }

theorem u17248 : Upper (D 6) (R 6) [10,160,48,260,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17249 : Route 9 := (fun mask => (mask,id))

def c17249 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17249 : Upper (D 6) (R 6) [10,160,48,260,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,48,260,66,1] 13 (by decide) (choices 1) [1,4] r17249 c17249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4581
  · exact u4582

def b17250 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 52 268 82 36 65 193 321), lower := (rows 11 162 52 268 82 36 64 128 256), losses := [] }

theorem u17250 : Upper (D 6) (R 6) [10,160,48,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17251 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 52 268 82 96 69 133 261), lower := (rows 11 162 52 268 82 96 64 128 256), losses := [] }

theorem u17251 : Upper (D 6) (R 6) [10,160,48,260,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17252 : Route 9 := (fun mask => (mask,id))

def c17252 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17252 : Upper (D 6) (R 6) [10,160,48,260,68,1] 13 := by
  apply FastRouting.sound _ _ [10,160,48,260,68,1] 13 (by decide) (choices 1) [1,2] r17252 c17252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4583
  · exact u4584

def b17253 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 268 84 34 65 193 321), lower := (rows 11 162 52 268 84 34 64 128 256), losses := [] }

theorem u17253 : Upper (D 6) (R 6) [10,160,48,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17254 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 52 268 84 96 67 131 259), lower := (rows 11 162 52 268 84 96 64 128 256), losses := [] }

theorem u17254 : Upper (D 6) (R 6) [10,160,48,260,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17255 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 162 52 328 21 33 70 198 326), lower := (rows 11 162 52 328 21 33 64 128 256), losses := [] }

theorem u17255 : Upper (D 6) (R 6) [10,160,48,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17256 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 328 21 34 69 197 325), lower := (rows 11 162 52 328 21 34 64 128 256), losses := [] }

theorem u17256 : Upper (D 6) (R 6) [10,160,48,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17257 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 52, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 162 52 328 21 36 67 195 323), lower := (rows 11 162 52 328 21 36 64 128 256), losses := [] }

theorem u17257 : Upper (D 6) (R 6) [10,160,48,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17258 : PairBound 9 := { available := 7, camps := [], pairs := [(1,6),(2,1),(4,1)], upper := (rows 11 162 52 328 21 96 71 135 263), lower := (rows 11 162 52 328 21 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 104 64 128 256), good := (rows 61 160 52 360 21 96 96 128 256) },{ target := 6, region := (rows 1 6 4 8 16 32 0 144 272), good := (rows 11 162 438 264 407 32 0 128 256) }] }

theorem u17258 : Upper (D 6) (R 6) [10,160,48,320,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17259 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 458, targets := 1 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 11 162 52 328 81 33 70 134 262), lower := (rows 11 162 52 328 81 33 64 128 256), losses := [] }

theorem u17259 : Upper (D 6) (R 6) [10,160,48,320,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17260 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 328 81 34 69 133 261), lower := (rows 11 162 52 328 81 34 64 128 256), losses := [] }

theorem u17260 : Upper (D 6) (R 6) [10,160,48,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17261 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,0),(2,1)], upper := (rows 11 162 52 328 81 36 71 135 263), lower := (rows 11 162 52 328 81 36 64 128 256), losses := [] }

theorem u17261 : Upper (D 6) (R 6) [10,160,48,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17262 : Route 9 := (fun mask => (mask,id))

def c17262 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17262 : Upper (D 6) (R 6) [10,160,48,320,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,48,320,66,1] 13 (by decide) (choices 1) [1,4] r17262 c17262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4585
  · exact u4586

def b17263 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 52 328 82 36 69 133 261), lower := (rows 11 162 52 328 82 36 64 128 256), losses := [] }

theorem u17263 : Upper (D 6) (R 6) [10,160,48,320,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17264 : Route 9 := (fun mask => (mask,id))

def c17264 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17264 : Upper (D 6) (R 6) [10,160,48,320,68,1] 13 := by
  apply FastRouting.sound _ _ [10,160,48,320,68,1] 13 (by decide) (choices 1) [1,2,4] r17264 c17264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4587
  · exact u4588
  · exact u4589

def b17265 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 52 328 84 34 69 133 261), lower := (rows 11 162 52 328 84 34 64 128 256), losses := [] }

theorem u17265 : Upper (D 6) (R 6) [10,160,48,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17266 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 52 328 84 36 67 131 259), lower := (rows 11 162 52 328 84 36 64 128 256), losses := [] }

theorem u17266 : Upper (D 6) (R 6) [10,160,48,320,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17267 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 25 276 34 100 228 356), lower := (rows 11 162 69 25 276 34 64 128 256), losses := [] }

theorem u17267 : Upper (D 6) (R 6) [10,160,65,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17268 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 5, region := 194, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 162 69 25 276 36 98 226 354), lower := (rows 11 162 69 25 276 36 64 128 256), losses := [] }

theorem u17268 : Upper (D 6) (R 6) [10,160,65,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17269 : Route 9 := (fun mask => (mask,id))

def c17269 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17269 : Upper (D 6) (R 6) [10,160,65,17,260,64] 13 := by
  apply FastRouting.sound _ _ [10,160,65,17,260,64] 13 (by decide) (choices 1) [2,4,32] r17269 c17269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4590
  · exact u4591
  · exact u4592

def b17270 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 28 273 34 100 228 356), lower := (rows 11 162 69 28 273 34 64 128 256), losses := [] }

theorem u17270 : Upper (D 6) (R 6) [10,160,65,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17271 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 194, targets := 5 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 11 162 69 28 273 36 98 226 354), lower := (rows 11 162 69 28 273 36 64 128 256), losses := [{ target := 2, region := (rows 1 34 0 8 17 32 98 162 290), good := (rows 475 482 81 24 273 482 64 128 256) }] }

theorem u17271 : Upper (D 6) (R 6) [10,160,65,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17272 : Route 9 := (fun mask => (mask,id))

def c17272 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17272 : Upper (D 6) (R 6) [10,160,65,20,257,64] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,257,64] 13 (by decide) (choices 1) [2,4,32] r17272 c17272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4593
  · exact u4594
  · exact u4595

def r17273 : Route 9 := (fun mask => (mask,id))

def c17273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17273 : Upper (D 6) (R 6) [10,160,65,20,258,1] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,258,1] 13 (by decide) (choices 1) [4,32] r17273 c17273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4596
  · exact u4597

def r17274 : Route 9 := (fun mask => (mask,id))

def c17274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17274 : Upper (D 6) (R 6) [10,160,65,20,258,4] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,258,4] 13 (by decide) (choices 1) [1,32] r17274 c17274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4598
  · exact u4599

def r17275 : Route 9 := (fun mask => (mask,id))

def c17275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17275 : Upper (D 6) (R 6) [10,160,65,20,258,64] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,258,64] 13 (by decide) (choices 1) [1,4,32] r17275 c17275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4600
  · exact u4601
  · exact u4602

def r17276 : Route 9 := (fun mask => (mask,id))

def c17276 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17276 : Upper (D 6) (R 6) [10,160,65,20,288,1] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,288,1] 13 (by decide) (choices 1) [2,4] r17276 c17276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4603
  · exact u4604

def b17277 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 28 304 34 69 197 325), lower := (rows 11 162 69 28 304 34 64 128 256), losses := [] }

theorem u17277 : Upper (D 6) (R 6) [10,160,65,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17278 : Route 9 := (fun mask => (mask,id))

def c17278 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17278 : Upper (D 6) (R 6) [10,160,65,20,288,4] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,288,4] 13 (by decide) (choices 1) [1,2] r17278 c17278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4605
  · exact u4606

def r17279 : Route 9 := (fun mask => (mask,id))

def c17279 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17279 : Upper (D 6) (R 6) [10,160,65,20,288,64] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,288,64] 13 (by decide) (choices 1) [1,2,4] r17279 c17279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4607
  · exact u4608
  · exact u4609

#print axioms u17279
end Delivery.IrregularNine14.P06
