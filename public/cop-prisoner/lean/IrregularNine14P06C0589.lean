import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0317
import IrregularNine14P06C0318
import IrregularNine14P06C0319

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35340 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 25 98 164 14 82 293 325 389 261), lower := (rows 25 98 164 14 82 32 64 128 256), losses := [] }

theorem u35340 : Upper (D 6) (R 6) [24,96,160,6,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35341 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 337, targets := 32 },{ cop := 0, region := 354, targets := 4 }], pairs := [(0,5),(1,2),(4,5)], upper := (rows 25 98 164 14 84 291 323 387 259), lower := (rows 25 98 164 14 84 32 64 128 256), losses := [] }

theorem u35341 : Upper (D 6) (R 6) [24,96,160,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35342 : Route 9 := (fun mask => (mask,id))

def c35342 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35342 : Upper (D 6) (R 6) [24,96,160,6,257] 13 := by
  apply FastRouting.sound _ _ [24,96,160,6,257] 13 (by decide) (choices 1) [1,2,4,64] r35342 c35342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19079
  · exact u19080
  · exact u19081
  · exact u19082

def b35343 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 337, targets := 32 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,5),(2,1),(4,5)], upper := (rows 25 98 164 14 274 101 69 197 325), lower := (rows 25 98 164 14 274 32 64 128 256), losses := [] }

theorem u35343 : Upper (D 6) (R 6) [24,96,160,6,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35344 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 337, targets := 32 },{ cop := 0, region := 98, targets := 4 }], pairs := [(0,5),(1,2),(4,5)], upper := (rows 25 98 164 14 276 99 67 195 323), lower := (rows 25 98 164 14 276 32 64 128 256), losses := [] }

theorem u35344 : Upper (D 6) (R 6) [24,96,160,6,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35345 : Route 9 := (fun mask => (mask,id))

def c35345 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35345 : Upper (D 6) (R 6) [24,96,160,6,320] 13 := by
  apply FastRouting.sound _ _ [24,96,160,6,320] 13 (by decide) (choices 1) [1,2,4] r35345 c35345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19083
  · exact u19084
  · exact u19085

def b35346 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 25 98 164 73 273 38 70 134 262), lower := (rows 25 98 164 73 273 32 64 128 256), losses := [] }

theorem u35346 : Upper (D 6) (R 6) [24,96,160,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35347 : Route 9 := (fun mask => (mask,id))

def c35347 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35347 : Upper (D 6) (R 6) [24,96,160,65,258] 13 := by
  apply FastRouting.sound _ _ [24,96,160,65,258] 13 (by decide) (choices 1) [1,2,4] r35347 c35347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19086
  · exact u19087
  · exact u19088

def r35348 : Route 9 := (fun mask => (mask,id))

def c35348 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35348 : Upper (D 6) (R 6) [24,96,160,65,260] 13 := by
  apply FastRouting.sound _ _ [24,96,160,65,260] 13 (by decide) (choices 1) [1,2,4] r35348 c35348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19089
  · exact u19090
  · exact u19091

def b35349 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 25 98 164 74 273 39 71 135 263), lower := (rows 25 98 164 74 273 32 64 128 256), losses := [] }

theorem u35349 : Upper (D 6) (R 6) [24,96,160,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35350 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 25 98 164 74 274 37 69 133 261), lower := (rows 25 98 164 74 274 32 64 128 256), losses := [] }

theorem u35350 : Upper (D 6) (R 6) [24,96,160,66,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35351 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 25 98 164 74 276 39 71 135 263), lower := (rows 25 98 164 74 276 32 64 128 256), losses := [] }

theorem u35351 : Upper (D 6) (R 6) [24,96,160,66,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35352 : Route 9 := (fun mask => (mask,id))

def c35352 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35352 : Upper (D 6) (R 6) [24,96,160,68,257] 13 := by
  apply FastRouting.sound _ _ [24,96,160,68,257] 13 (by decide) (choices 1) [1,2,4] r35352 c35352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19092
  · exact u19093
  · exact u19094

def r35353 : Route 9 := (fun mask => (mask,id))

def c35353 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35353 : Upper (D 6) (R 6) [24,96,160,68,258] 13 := by
  apply FastRouting.sound _ _ [24,96,160,68,258] 13 (by decide) (choices 1) [1,2,4] r35353 c35353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19095
  · exact u19096
  · exact u19097

def r35354 : Route 9 := (fun mask => (mask,id))

def c35354 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35354 : Upper (D 6) (R 6) [24,96,160,68,260] 13 := by
  apply FastRouting.sound _ _ [24,96,160,68,260] 13 (by decide) (choices 1) [1,2] r35354 c35354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19098
  · exact u19099

def b35355 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 98 388 11 19 100 100 228 356), lower := (rows 25 98 388 11 19 32 64 128 256), losses := [] }

theorem u35355 : Upper (D 6) (R 6) [24,96,384,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35356 : Route 9 := (fun mask => (mask,id))

def c35356 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35356 : Upper (D 6) (R 6) [24,96,384,3,5] 13 := by
  apply FastRouting.sound _ _ [24,96,384,3,5] 13 (by decide) (choices 1) [2,4,64] r35356 c35356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19100
  · exact u19101
  · exact u19102

def b35357 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 98 388 11 22 101 101 229 357), lower := (rows 25 98 388 11 22 32 64 128 256), losses := [] }

theorem u35357 : Upper (D 6) (R 6) [24,96,384,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35358 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 98 388 11 49 102 70 198 326), lower := (rows 25 98 388 11 49 32 64 128 256), losses := [] }

theorem u35358 : Upper (D 6) (R 6) [24,96,384,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35359 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 98 388 11 50 101 69 197 325), lower := (rows 25 98 388 11 50 32 64 128 256), losses := [] }

theorem u35359 : Upper (D 6) (R 6) [24,96,384,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35360 : Route 9 := (fun mask => (mask,id))

def c35360 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35360 : Upper (D 6) (R 6) [24,96,384,3,36] 13 := by
  apply FastRouting.sound _ _ [24,96,384,3,36] 13 (by decide) (choices 1) [1,2,4,64] r35360 c35360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19103
  · exact u19104
  · exact u19105
  · exact u19106

def b35361 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 98 388 11 112 39 71 135 263), lower := (rows 25 98 388 11 112 32 64 128 256), losses := [] }

theorem u35361 : Upper (D 6) (R 6) [24,96,384,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35362 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 25, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 388 13 21 98 98 226 354), lower := (rows 25 98 388 13 21 32 64 128 256), losses := [] }

theorem u35362 : Upper (D 6) (R 6) [24,96,384,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35363 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 388 13 22 99 99 227 355), lower := (rows 25 98 388 13 22 32 64 128 256), losses := [] }

theorem u35363 : Upper (D 6) (R 6) [24,96,384,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35364 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 486, targets := 1 },{ cop := 1, region := 388, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 25 98 388 13 49 102 70 198 326), lower := (rows 25 98 388 13 49 32 64 128 256), losses := [] }

theorem u35364 : Upper (D 6) (R 6) [24,96,384,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35365 : PairBound 9 := { available := 71, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 98 388 13 50 103 71 199 327), lower := (rows 25 98 388 13 50 32 64 128 256), losses := [] }

theorem u35365 : Upper (D 6) (R 6) [24,96,384,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35366 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 98 388 13 52 99 67 195 323), lower := (rows 25 98 388 13 52 32 64 128 256), losses := [] }

theorem u35366 : Upper (D 6) (R 6) [24,96,384,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35367 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 25 98 388 13 112 39 71 135 263), lower := (rows 25 98 388 13 112 32 64 128 256), losses := [] }

theorem u35367 : Upper (D 6) (R 6) [24,96,384,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35368 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 17, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 98 388 14 22 97 97 225 353), lower := (rows 25 98 388 14 22 32 64 128 256), losses := [] }

theorem u35368 : Upper (D 6) (R 6) [24,96,384,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35369 : Route 9 := (fun mask => (mask,id))

def c35369 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35369 : Upper (D 6) (R 6) [24,96,384,6,33] 13 := by
  apply FastRouting.sound _ _ [24,96,384,6,33] 13 (by decide) (choices 1) [1,2,4,64] r35369 c35369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19107
  · exact u19108
  · exact u19109
  · exact u19110

def b35370 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 98 388 14 50 101 69 197 325), lower := (rows 25 98 388 14 50 32 64 128 256), losses := [] }

theorem u35370 : Upper (D 6) (R 6) [24,96,384,6,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35371 : Route 9 := (fun mask => (mask,id))

def c35371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35371 : Upper (D 6) (R 6) [24,96,384,6,36] 13 := by
  apply FastRouting.sound _ _ [24,96,384,6,36] 13 (by decide) (choices 1) [1,2,64] r35371 c35371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19111
  · exact u19112
  · exact u19113

def b35372 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 16, targets := 5 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,2)], upper := (rows 25 98 388 14 112 39 71 135 263), lower := (rows 25 98 388 14 112 32 64 128 256), losses := [] }

theorem u35372 : Upper (D 6) (R 6) [24,96,384,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35373 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 25, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 98 388 41 81 38 70 134 262), lower := (rows 25 98 388 41 81 32 64 128 256), losses := [] }

theorem u35373 : Upper (D 6) (R 6) [24,96,384,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35374 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 25, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 98 388 41 82 39 71 135 263), lower := (rows 25 98 388 41 82 32 64 128 256), losses := [] }

theorem u35374 : Upper (D 6) (R 6) [24,96,384,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35375 : Route 9 := (fun mask => (mask,id))

def c35375 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35375 : Upper (D 6) (R 6) [24,96,384,33,68] 13 := by
  apply FastRouting.sound _ _ [24,96,384,33,68] 13 (by decide) (choices 1) [1,2,4] r35375 c35375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19114
  · exact u19115
  · exact u19116

def b35376 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 8, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 25 98 388 42 84 39 71 135 263), lower := (rows 25 98 388 42 84 32 64 128 256), losses := [] }

theorem u35376 : Upper (D 6) (R 6) [24,96,384,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35377 : Route 9 := (fun mask => (mask,id))

def c35377 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35377 : Upper (D 6) (R 6) [24,96,384,36,68] 13 := by
  apply FastRouting.sound _ _ [24,96,384,36,68] 13 (by decide) (choices 1) [1,2] r35377 c35377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19117
  · exact u19118

def b35378 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 17, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 131 261 14 22 96 96 224 352), lower := (rows 25 131 261 14 22 32 64 128 256), losses := [] }

theorem u35378 : Upper (D 6) (R 6) [24,129,257,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35379 : Route 9 := (fun mask => (mask,id))

def c35379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35379 : Upper (D 6) (R 6) [24,129,257,6,34] 13 := by
  apply FastRouting.sound _ _ [24,129,257,6,34] 13 (by decide) (choices 1) [4,64] r35379 c35379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19119
  · exact u19120

theorem m35380_4 : Upper (D 6) (R 6) [24,129,257,6,96,4] 13 :=
  permutation_upper _ _ _ [24,129,257,6,96,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19121

def r35380 : Route 9 := (fun mask => (mask,id))

def c35380 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35380 : Upper (D 6) (R 6) [24,129,257,6,96] 13 := by
  apply FastRouting.sound _ _ [24,129,257,6,96] 13 (by decide) (choices 1) [2,4,64] r35380 c35380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19121
  · exact m35380_4
  · exact u19122

def b35381 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 17, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 25 131 261 42 50 100 68 196 324), lower := (rows 25 131 261 42 50 32 64 128 256), losses := [] }

theorem u35381 : Upper (D 6) (R 6) [24,129,257,34,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m35382_4 : Upper (D 6) (R 6) [24,129,257,34,36,4] 13 :=
  permutation_upper _ _ _ [24,129,257,34,36,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u19123

def r35382 : Route 9 := (fun mask => (mask,id))

def c35382 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35382 : Upper (D 6) (R 6) [24,129,257,34,36] 13 := by
  apply FastRouting.sound _ _ [24,129,257,34,36] 13 (by decide) (choices 1) [2,4,64] r35382 c35382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19123
  · exact m35382_4
  · exact u19124

def r35383 : Route 9 := (fun mask => (mask,id))

def c35383 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35383 : Upper (D 6) (R 6) [24,129,257,34,66] 13 := by
  apply FastRouting.sound _ _ [24,129,257,34,66] 13 (by decide) (choices 1) [4,64] r35383 c35383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19125
  · exact u19126

def r35384 : Route 9 := (fun mask => (mask,id))

def c35384 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35384 : Upper (D 6) (R 6) [24,129,257,34,68] 13 := by
  apply FastRouting.sound _ _ [24,129,257,34,68] 13 (by decide) (choices 1) [2,4,64] r35384 c35384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19127
  · exact u19128
  · exact u19129

def r35385 : Route 9 := (fun mask => (mask,id))

def c35385 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35385 : Upper (D 6) (R 6) [24,129,257,34,96] 13 := by
  apply FastRouting.sound _ _ [24,129,257,34,96] 13 (by decide) (choices 1) [2,4,64] r35385 c35385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19130
  · exact u19131
  · exact u19132

def b35386 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 17, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 131 261 104 112 38 70 134 262), lower := (rows 25 131 261 104 112 32 64 128 256), losses := [] }

theorem u35386 : Upper (D 6) (R 6) [24,129,257,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35387 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 131 262 11 52 100 100 228 356), lower := (rows 25 131 262 11 52 32 64 128 256), losses := [] }

theorem u35387 : Upper (D 6) (R 6) [24,129,258,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35388 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 25 131 262 11 112 100 100 228 356), lower := (rows 25 131 262 11 112 32 64 128 256), losses := [] }

theorem u35388 : Upper (D 6) (R 6) [24,129,258,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35389 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 131 262 13 22 96 96 224 352), lower := (rows 25 131 262 13 22 32 64 128 256), losses := [] }

theorem u35389 : Upper (D 6) (R 6) [24,129,258,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35390 : Route 9 := (fun mask => (mask,id))

def c35390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35390 : Upper (D 6) (R 6) [24,129,258,5,34] 13 := by
  apply FastRouting.sound _ _ [24,129,258,5,34] 13 (by decide) (choices 1) [4,64] r35390 c35390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19133
  · exact u19134

def b35391 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 9, targets := 98 }], pairs := [(0,1),(0,5),(0,6)], upper := (rows 25 131 262 13 52 98 98 226 354), lower := (rows 25 131 262 13 52 32 64 128 256), losses := [] }

theorem u35391 : Upper (D 6) (R 6) [24,129,258,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35392 : Route 9 := (fun mask => (mask,id))

def c35392 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35392 : Upper (D 6) (R 6) [24,129,258,5,96] 13 := by
  apply FastRouting.sound _ _ [24,129,258,5,96] 13 (by decide) (choices 1) [2,4,64] r35392 c35392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19135
  · exact u19136
  · exact u19137

def b35393 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 364, targets := 1 },{ cop := 2, region := 8, targets := 32 }], pairs := [(2,0),(3,0),(3,5)], upper := (rows 25 131 262 14 49 100 100 228 356), lower := (rows 25 131 262 14 49 32 64 128 256), losses := [] }

theorem u35393 : Upper (D 6) (R 6) [24,129,258,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35394 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 131 262 14 52 97 97 225 353), lower := (rows 25 131 262 14 52 32 64 128 256), losses := [] }

theorem u35394 : Upper (D 6) (R 6) [24,129,258,6,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35395 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 25 131 262 14 112 101 101 229 357), lower := (rows 25 131 262 14 112 32 64 128 256), losses := [] }

theorem u35395 : Upper (D 6) (R 6) [24,129,258,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35396 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 131 262 41 50 100 68 196 324), lower := (rows 25 131 262 41 50 32 64 128 256), losses := [] }

theorem u35396 : Upper (D 6) (R 6) [24,129,258,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b35397 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 9, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 131 262 41 52 102 70 198 326), lower := (rows 25 131 262 41 52 32 64 128 256), losses := [] }

theorem u35397 : Upper (D 6) (R 6) [24,129,258,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b35397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r35398 : Route 9 := (fun mask => (mask,id))

def c35398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35398 : Upper (D 6) (R 6) [24,129,258,33,66] 13 := by
  apply FastRouting.sound _ _ [24,129,258,33,66] 13 (by decide) (choices 1) [4,64] r35398 c35398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u19138
  · exact u19139

def r35399 : Route 9 := (fun mask => (mask,id))

def c35399 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u35399 : Upper (D 6) (R 6) [24,129,258,33,68] 13 := by
  apply FastRouting.sound _ _ [24,129,258,33,68] 13 (by decide) (choices 1) [2,4,64] r35399 c35399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19140
  · exact u19141
  · exact u19142

#print axioms u35399
end Delivery.IrregularNine14.P06
