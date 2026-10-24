import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0315
import IrregularNine14P06C0316

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35220 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 388 14 81 99 99 227 355), lower := (rows 25 38 388 14 81 32 64 128 256), losses := [] }

theorem u35220 : Upper (D 6) (R 6) [24,36,384,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35221 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 388 14 82 97 97 225 353), lower := (rows 25 38 388 14 82 32 64 128 256), losses := [] }

theorem u35221 : Upper (D 6) (R 6) [24,36,384,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35222 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 38 388 14 112 99 67 195 323), lower := (rows 25 38 388 14 112 32 64 128 256), losses := [] }

theorem u35222 : Upper (D 6) (R 6) [24,36,384,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35223 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 1, region := 452, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 38 388 41 81 102 70 198 326), lower := (rows 25 38 388 41 81 32 64 128 256), losses := [] }

theorem u35223 : Upper (D 6) (R 6) [24,36,384,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35224 : Route 9 := (fun mask => (mask,id))

def c35224 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35224 : Upper (D 6) (R 6) [24,36,384,33,66] 13 := by
  apply FastRouting.sound _ _ [24,36,384,33,66] 13 (by decide) (choices 1) [1,2,4,64] r35224 c35224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18934
  · exact u18935
  · exact u18936
  · exact u18937

def r35225 : Route 9 := (fun mask => (mask,id))

def c35225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35225 : Upper (D 6) (R 6) [24,36,384,33,68] 13 := by
  apply FastRouting.sound _ _ [24,36,384,33,68] 13 (by decide) (choices 1) [1,2,64] r35225 c35225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18938
  · exact u18939
  · exact u18940

def b35226 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 388 42 81 103 71 199 327), lower := (rows 25 38 388 42 81 32 64 128 256), losses := [] }

theorem u35226 : Upper (D 6) (R 6) [24,36,384,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35227 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 388 42 82 101 69 197 325), lower := (rows 25 38 388 42 82 32 64 128 256), losses := [] }

theorem u35227 : Upper (D 6) (R 6) [24,36,384,34,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35228 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 38 388 42 84 99 67 195 323), lower := (rows 25 38 388 42 84 32 64 128 256), losses := [] }

theorem u35228 : Upper (D 6) (R 6) [24,36,384,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35229 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 388 44 81 99 67 195 323), lower := (rows 25 38 388 44 81 32 64 128 256), losses := [] }

theorem u35229 : Upper (D 6) (R 6) [24,36,384,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35230 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 8, targets := 65 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,6)], upper := (rows 25 38 388 44 82 99 67 195 323), lower := (rows 25 38 388 44 82 32 64 128 256), losses := [] }

theorem u35230 : Upper (D 6) (R 6) [24,36,384,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35231 : PairBound 9 := { available := 38, camps := [{ cop := 6, region := 25, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 388 73 81 38 102 166 294), lower := (rows 25 38 388 73 81 32 64 128 256), losses := [] }

theorem u35231 : Upper (D 6) (R 6) [24,36,384,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35232 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 388 73 82 39 103 167 295), lower := (rows 25 38 388 73 82 32 64 128 256), losses := [] }

theorem u35232 : Upper (D 6) (R 6) [24,36,384,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35233 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 388 73 84 35 99 163 291), lower := (rows 25 38 388 73 84 32 64 128 256), losses := [] }

theorem u35233 : Upper (D 6) (R 6) [24,36,384,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35234 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 9, targets := 38 }], pairs := [(0,1),(0,2),(0,5)], upper := (rows 25 38 388 73 112 39 71 135 263), lower := (rows 25 38 388 73 112 32 64 128 256), losses := [] }

theorem u35234 : Upper (D 6) (R 6) [24,36,384,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35235 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 38 388 74 82 37 101 165 293), lower := (rows 25 38 388 74 82 32 64 128 256), losses := [] }

theorem u35235 : Upper (D 6) (R 6) [24,36,384,66,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35236 : Route 9 := (fun mask => (mask,id))

def c35236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35236 : Upper (D 6) (R 6) [24,36,384,66,68] 13 := by
  apply FastRouting.sound _ _ [24,36,384,66,68] 13 (by decide) (choices 1) [1,2] r35236 c35236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18941
  · exact u18942

def r35237 : Route 9 := (fun mask => (mask,id))

def c35237 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35237 : Upper (D 6) (R 6) [24,36,384,66,96] 13 := by
  apply FastRouting.sound _ _ [24,36,384,66,96] 13 (by decide) (choices 1) [1,2,4] r35237 c35237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18943
  · exact u18944
  · exact u18945

def r35238 : Route 9 := (fun mask => (mask,id))

def c35238 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35238 : Upper (D 6) (R 6) [24,36,384,68,96] 13 := by
  apply FastRouting.sound _ _ [24,36,384,68,96] 13 (by decide) (choices 1) [1,2] r35238 c35238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18946
  · exact u18947

def b35239 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 98 133 11 22 356 356 484 356), lower := (rows 25 98 133 11 22 32 64 128 256), losses := [] }

theorem u35239 : Upper (D 6) (R 6) [24,96,129,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35240 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 98 133 11 50 356 324 452 324), lower := (rows 25 98 133 11 50 32 64 128 256), losses := [] }

theorem u35240 : Upper (D 6) (R 6) [24,96,129,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35241 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 3, region := 452, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 25 98 133 11 52 358 326 454 326), lower := (rows 25 98 133 11 52 32 64 128 256), losses := [] }

theorem u35241 : Upper (D 6) (R 6) [24,96,129,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35242 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 98 133 11 112 294 326 390 262), lower := (rows 25 98 133 11 112 32 64 128 256), losses := [] }

theorem u35242 : Upper (D 6) (R 6) [24,96,129,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35243 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 98 133 11 274 100 100 228 356), lower := (rows 25 98 133 11 274 32 64 128 256), losses := [] }

theorem u35243 : Upper (D 6) (R 6) [24,96,129,3,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35244 : Route 9 := (fun mask => (mask,id))

def c35244 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35244 : Upper (D 6) (R 6) [24,96,129,3,260] 13 := by
  apply FastRouting.sound _ _ [24,96,129,3,260] 13 (by decide) (choices 1) [2,4,64] r35244 c35244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18948
  · exact u18949
  · exact u18950

def b35245 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 3, region := 196, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 25 98 133 11 304 102 70 198 326), lower := (rows 25 98 133 11 304 32 64 128 256), losses := [] }

theorem u35245 : Upper (D 6) (R 6) [24,96,129,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35246 : PairBound 9 := { available := 354, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 133 13 22 354 354 482 354), lower := (rows 25 98 133 13 22 32 64 128 256), losses := [] }

theorem u35246 : Upper (D 6) (R 6) [24,96,129,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35247 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 133 13 52 354 322 450 322), lower := (rows 25 98 133 13 52 32 64 128 256), losses := [] }

theorem u35247 : Upper (D 6) (R 6) [24,96,129,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35248 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 25 98 133 13 274 102 102 230 358), lower := (rows 25 98 133 13 274 32 64 128 256), losses := [] }

theorem u35248 : Upper (D 6) (R 6) [24,96,129,5,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35249 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 133 13 276 98 98 226 354), lower := (rows 25 98 133 13 276 32 64 128 256), losses := [] }

theorem u35249 : Upper (D 6) (R 6) [24,96,129,5,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35250 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 25 98 133 13 304 102 70 198 326), lower := (rows 25 98 133 13 304 32 64 128 256), losses := [] }

theorem u35250 : Upper (D 6) (R 6) [24,96,129,5,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35251 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 17, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 98 133 14 22 353 353 481 353), lower := (rows 25 98 133 14 22 32 64 128 256), losses := [] }

theorem u35251 : Upper (D 6) (R 6) [24,96,129,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35252 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 362, targets := 1 }], pairs := [(1,0),(2,5),(3,0)], upper := (rows 25 98 133 14 49 358 326 454 326), lower := (rows 25 98 133 14 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 8 16 0 72 136 264), good := (rows 477 66 133 462 21 0 64 128 256) }] }

theorem u35252 : Upper (D 6) (R 6) [24,96,129,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35253 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 98 133 14 50 357 325 453 325), lower := (rows 25 98 133 14 50 32 64 128 256), losses := [] }

theorem u35253 : Upper (D 6) (R 6) [24,96,129,6,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35254 : Route 9 := (fun mask => (mask,id))

def c35254 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u35254 : Upper (D 6) (R 6) [24,96,129,6,36] 13 := by
  apply FastRouting.sound _ _ [24,96,129,6,36] 13 (by decide) (choices 1) [1,2,64,256] r35254 c35254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18951
  · exact u18952
  · exact u18953
  · exact u18954

def b35255 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 25 98 133 14 112 295 327 391 263), lower := (rows 25 98 133 14 112 32 64 128 256), losses := [] }

theorem u35255 : Upper (D 6) (R 6) [24,96,129,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35256 : Route 9 := (fun mask => (mask,id))

def c35256 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35256 : Upper (D 6) (R 6) [24,96,129,6,257] 13 := by
  apply FastRouting.sound _ _ [24,96,129,6,257] 13 (by decide) (choices 1) [2,4,64] r35256 c35256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18955
  · exact u18956
  · exact u18957

def r35257 : Route 9 := (fun mask => (mask,id))

def c35257 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35257 : Upper (D 6) (R 6) [24,96,129,6,258] 13 := by
  apply FastRouting.sound _ _ [24,96,129,6,258] 13 (by decide) (choices 1) [1,4,64] r35257 c35257
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18958
  · exact u18959
  · exact u18960

def r35258 : Route 9 := (fun mask => (mask,id))

def c35258 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35258 : Upper (D 6) (R 6) [24,96,129,6,260] 13 := by
  apply FastRouting.sound _ _ [24,96,129,6,260] 13 (by decide) (choices 1) [1,2,64] r35258 c35258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18961
  · exact u18962
  · exact u18963

def r35259 : Route 9 := (fun mask => (mask,id))

def c35259 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35259 : Upper (D 6) (R 6) [24,96,129,6,288] 13 := by
  apply FastRouting.sound _ _ [24,96,129,6,288] 13 (by decide) (choices 1) [1,2,4,64] r35259 c35259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18964
  · exact u18965
  · exact u18966
  · exact u18967

def b35260 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 98 133 41 82 294 326 390 262), lower := (rows 25 98 133 41 82 32 64 128 256), losses := [] }

theorem u35260 : Upper (D 6) (R 6) [24,96,129,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35261 : Route 9 := (fun mask => (mask,id))

def c35261 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35261 : Upper (D 6) (R 6) [24,96,129,33,68] 13 := by
  apply FastRouting.sound _ _ [24,96,129,33,68] 13 (by decide) (choices 1) [2,4,256] r35261 c35261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18968
  · exact u18969
  · exact u18970

def r35262 : Route 9 := (fun mask => (mask,id))

def c35262 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35262 : Upper (D 6) (R 6) [24,96,129,33,258] 13 := by
  apply FastRouting.sound _ _ [24,96,129,33,258] 13 (by decide) (choices 1) [2,4,64] r35262 c35262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18971
  · exact u18972
  · exact u18973

def r35263 : Route 9 := (fun mask => (mask,id))

def c35263 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35263 : Upper (D 6) (R 6) [24,96,129,33,260] 13 := by
  apply FastRouting.sound _ _ [24,96,129,33,260] 13 (by decide) (choices 1) [2,4,64] r35263 c35263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18974
  · exact u18975
  · exact u18976

def r35264 : Route 9 := (fun mask => (mask,id))

def c35264 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35264 : Upper (D 6) (R 6) [24,96,129,33,320] 13 := by
  apply FastRouting.sound _ _ [24,96,129,33,320] 13 (by decide) (choices 1) [2,4] r35264 c35264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u18977
  · exact u18978

def b35265 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 98 133 42 84 295 327 391 263), lower := (rows 25 98 133 42 84 32 64 128 256), losses := [] }

theorem u35265 : Upper (D 6) (R 6) [24,96,129,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35266 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 98 133 42 273 102 70 198 326), lower := (rows 25 98 133 42 273 32 64 128 256), losses := [] }

theorem u35266 : Upper (D 6) (R 6) [24,96,129,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35267 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 98 133 42 274 101 69 197 325), lower := (rows 25 98 133 42 274 32 64 128 256), losses := [] }

theorem u35267 : Upper (D 6) (R 6) [24,96,129,34,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35268 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 98 133 42 276 103 71 199 327), lower := (rows 25 98 133 42 276 32 64 128 256), losses := [] }

theorem u35268 : Upper (D 6) (R 6) [24,96,129,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35269 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 98 133 42 336 39 71 135 263), lower := (rows 25 98 133 42 336 32 64 128 256), losses := [] }

theorem u35269 : Upper (D 6) (R 6) [24,96,129,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35270 : Route 9 := (fun mask => (mask,id))

def c35270 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u35270 : Upper (D 6) (R 6) [24,96,129,36,68] 13 := by
  apply FastRouting.sound _ _ [24,96,129,36,68] 13 (by decide) (choices 1) [1,2,256] r35270 c35270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18979
  · exact u18980
  · exact u18981

def r35271 : Route 9 := (fun mask => (mask,id))

def c35271 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35271 : Upper (D 6) (R 6) [24,96,129,36,257] 13 := by
  apply FastRouting.sound _ _ [24,96,129,36,257] 13 (by decide) (choices 1) [2,4,64] r35271 c35271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18982
  · exact u18983
  · exact u18984

def r35272 : Route 9 := (fun mask => (mask,id))

def c35272 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35272 : Upper (D 6) (R 6) [24,96,129,36,258] 13 := by
  apply FastRouting.sound _ _ [24,96,129,36,258] 13 (by decide) (choices 1) [1,2,4,64] r35272 c35272
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u18985
  · exact u18986
  · exact u18987
  · exact u18988

def r35273 : Route 9 := (fun mask => (mask,id))

def c35273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35273 : Upper (D 6) (R 6) [24,96,129,36,260] 13 := by
  apply FastRouting.sound _ _ [24,96,129,36,260] 13 (by decide) (choices 1) [1,2,64] r35273 c35273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18989
  · exact u18990
  · exact u18991

def r35274 : Route 9 := (fun mask => (mask,id))

def c35274 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35274 : Upper (D 6) (R 6) [24,96,129,36,320] 13 := by
  apply FastRouting.sound _ _ [24,96,129,36,320] 13 (by decide) (choices 1) [1,2,4] r35274 c35274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u18992
  · exact u18993
  · exact u18994

def b35275 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 25 98 133 104 273 38 70 134 262), lower := (rows 25 98 133 104 273 32 64 128 256), losses := [] }

theorem u35275 : Upper (D 6) (R 6) [24,96,129,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35276 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 25 98 133 104 274 39 71 135 263), lower := (rows 25 98 133 104 274 32 64 128 256), losses := [] }

theorem u35276 : Upper (D 6) (R 6) [24,96,129,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35277 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 8, targets := 5 },{ cop := 3, region := 2, targets := 1 }], pairs := [(1,0),(3,0),(3,2)], upper := (rows 25 98 133 104 276 39 71 135 263), lower := (rows 25 98 133 104 276 32 64 128 256), losses := [] }

theorem u35277 : Upper (D 6) (R 6) [24,96,129,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35278 : PairBound 9 := { available := 356, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 98 134 11 21 356 356 484 356), lower := (rows 25 98 134 11 21 32 64 128 256), losses := [] }

theorem u35278 : Upper (D 6) (R 6) [24,96,130,3,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35279 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 98 134 11 49 356 324 452 324), lower := (rows 25 98 134 11 49 32 64 128 256), losses := [] }

theorem u35279 : Upper (D 6) (R 6) [24,96,130,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u35279
end Delivery.IrregularNine14.P06
