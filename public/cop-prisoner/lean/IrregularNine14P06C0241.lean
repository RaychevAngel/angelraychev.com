import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0054

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14460 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 164 265 84 96 71 135 263), lower := (rows 11 50 164 265 84 96 64 128 256), losses := [] }

theorem u14460 : Upper (D 6) (R 6) [10,48,160,257,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14461 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 164 268 81 33 70 198 326), lower := (rows 11 50 164 268 81 33 64 128 256), losses := [] }

theorem u14461 : Upper (D 6) (R 6) [10,48,160,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14462 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 164 268 81 34 69 197 325), lower := (rows 11 50 164 268 81 34 64 128 256), losses := [] }

theorem u14462 : Upper (D 6) (R 6) [10,48,160,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14463 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 268 81 36 67 195 323), lower := (rows 11 50 164 268 81 36 64 128 256), losses := [] }

theorem u14463 : Upper (D 6) (R 6) [10,48,160,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14464 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 164 268 81 96 71 135 263), lower := (rows 11 50 164 268 81 96 64 128 256), losses := [] }

theorem u14464 : Upper (D 6) (R 6) [10,48,160,260,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14465 : Route 9 := (fun mask => (mask,id))

def c14465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14465 : Upper (D 6) (R 6) [10,48,160,260,66,1] 13 := by
  apply FastRouting.sound _ _ [10,48,160,260,66,1] 13 (by decide) (choices 1) [1,4] r14465 c14465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3251
  · exact u3252

def b14466 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 268 82 36 65 193 321), lower := (rows 11 50 164 268 82 36 64 128 256), losses := [] }

theorem u14466 : Upper (D 6) (R 6) [10,48,160,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14467 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 164 268 82 96 69 133 261), lower := (rows 11 50 164 268 82 96 64 128 256), losses := [] }

theorem u14467 : Upper (D 6) (R 6) [10,48,160,260,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14468 : Route 9 := (fun mask => (mask,id))

def c14468 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14468 : Upper (D 6) (R 6) [10,48,160,260,68,1] 13 := by
  apply FastRouting.sound _ _ [10,48,160,260,68,1] 13 (by decide) (choices 1) [1,2] r14468 c14468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3253
  · exact u3254

def b14469 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 164 268 84 34 65 193 321), lower := (rows 11 50 164 268 84 34 64 128 256), losses := [] }

theorem u14469 : Upper (D 6) (R 6) [10,48,160,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14470 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 164 268 84 96 67 131 259), lower := (rows 11 50 164 268 84 96 64 128 256), losses := [] }

theorem u14470 : Upper (D 6) (R 6) [10,48,160,260,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14471 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 164 328 21 33 70 198 326), lower := (rows 11 50 164 328 21 33 64 128 256), losses := [] }

theorem u14471 : Upper (D 6) (R 6) [10,48,160,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14472 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 164 328 21 34 69 197 325), lower := (rows 11 50 164 328 21 34 64 128 256), losses := [] }

theorem u14472 : Upper (D 6) (R 6) [10,48,160,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14473 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 164 328 21 36 67 195 323), lower := (rows 11 50 164 328 21 36 64 128 256), losses := [] }

theorem u14473 : Upper (D 6) (R 6) [10,48,160,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14474 : Route 9 := (fun mask => (mask,id))

def c14474 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14474 : Upper (D 6) (R 6) [10,48,160,320,5,64] 13 := by
  apply FastRouting.sound _ _ [10,48,160,320,5,64] 13 (by decide) (choices 1) [1,2,4] r14474 c14474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3255
  · exact u3256
  · exact u3257

def b14475 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 164 328 81 33 70 134 262), lower := (rows 11 50 164 328 81 33 64 128 256), losses := [] }

theorem u14475 : Upper (D 6) (R 6) [10,48,160,320,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14476 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 164 328 81 34 69 133 261), lower := (rows 11 50 164 328 81 34 64 128 256), losses := [] }

theorem u14476 : Upper (D 6) (R 6) [10,48,160,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14477 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 328 81 36 71 135 263), lower := (rows 11 50 164 328 81 36 64 128 256), losses := [] }

theorem u14477 : Upper (D 6) (R 6) [10,48,160,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14478 : Route 9 := (fun mask => (mask,id))

def c14478 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14478 : Upper (D 6) (R 6) [10,48,160,320,68,1] 13 := by
  apply FastRouting.sound _ _ [10,48,160,320,68,1] 13 (by decide) (choices 1) [1,2,4] r14478 c14478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3258
  · exact u3259
  · exact u3260

def b14479 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 164 328 84 34 69 133 261), lower := (rows 11 50 164 328 84 34 64 128 256), losses := [] }

theorem u14479 : Upper (D 6) (R 6) [10,48,160,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14480 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 164 328 84 36 67 131 259), lower := (rows 11 50 164 328 84 36 64 128 256), losses := [] }

theorem u14480 : Upper (D 6) (R 6) [10,48,160,320,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14481 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 196 13 81 34 356 420 292), lower := (rows 11 50 196 13 81 34 64 128 256), losses := [] }

theorem u14481 : Upper (D 6) (R 6) [10,48,192,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14482 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 11 50 196 13 81 36 354 418 290), lower := (rows 11 50 196 13 81 36 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 17 32 66 130 258), good := (rows 475 498 192 25 81 32 64 128 256) }] }

theorem u14482 : Upper (D 6) (R 6) [10,48,192,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14483 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 50 196 13 81 288 102 166 294), lower := (rows 11 50 196 13 81 288 64 128 256), losses := [] }

theorem u14483 : Upper (D 6) (R 6) [10,48,192,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14483 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14484 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 13 82 33 356 420 292), lower := (rows 11 50 196 13 82 33 64 128 256), losses := [] }

theorem u14484 : Upper (D 6) (R 6) [10,48,192,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14485 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 196 13 82 36 353 417 289), lower := (rows 11 50 196 13 82 36 64 128 256), losses := [] }

theorem u14485 : Upper (D 6) (R 6) [10,48,192,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14486 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 50 196 13 82 288 101 165 293), lower := (rows 11 50 196 13 82 288 64 128 256), losses := [] }

theorem u14486 : Upper (D 6) (R 6) [10,48,192,5,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14486 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14487 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 196 13 273 34 100 228 356), lower := (rows 11 50 196 13 273 34 64 128 256), losses := [] }

theorem u14487 : Upper (D 6) (R 6) [10,48,192,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14488 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 11 50 196 13 273 36 98 226 354), lower := (rows 11 50 196 13 273 36 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 17 32 66 130 258), good := (rows 475 498 192 25 273 32 64 128 256) }] }

theorem u14488 : Upper (D 6) (R 6) [10,48,192,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14489 : Route 9 := (fun mask => (mask,id))

def c14489 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14489 : Upper (D 6) (R 6) [10,48,192,5,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5,257,64] 13 (by decide) (choices 1) [2,4,32] r14489 c14489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3261
  · exact u3262
  · exact u3263

def b14490 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 13 274 33 100 228 356), lower := (rows 11 50 196 13 274 33 64 128 256), losses := [] }

theorem u14490 : Upper (D 6) (R 6) [10,48,192,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14491 : Route 9 := (fun mask => (mask,id))

def c14491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14491 : Upper (D 6) (R 6) [10,48,192,5,258,4] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5,258,4] 13 (by decide) (choices 1) [1,32] r14491 c14491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3264
  · exact u3265

def r14492 : Route 9 := (fun mask => (mask,id))

def c14492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14492 : Upper (D 6) (R 6) [10,48,192,5,258,64] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5,258,64] 13 (by decide) (choices 1) [1,4,32] r14492 c14492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3266
  · exact u3267
  · exact u3268

def b14493 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 196 13 276 33 98 226 354), lower := (rows 11 50 196 13 276 33 64 128 256), losses := [] }

theorem u14493 : Upper (D 6) (R 6) [10,48,192,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14494 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 196 13 276 34 97 225 353), lower := (rows 11 50 196 13 276 34 64 128 256), losses := [] }

theorem u14494 : Upper (D 6) (R 6) [10,48,192,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14495 : Route 9 := (fun mask => (mask,id))

def c14495 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14495 : Upper (D 6) (R 6) [10,48,192,5,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5,260,64] 13 (by decide) (choices 1) [1,2,32] r14495 c14495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3269
  · exact u3270
  · exact u3271

def b14496 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 13 336 33 102 166 294), lower := (rows 11 50 196 13 336 33 64 128 256), losses := [] }

theorem u14496 : Upper (D 6) (R 6) [10,48,192,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14497 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 196 13 336 34 101 165 293), lower := (rows 11 50 196 13 336 34 64 128 256), losses := [] }

theorem u14497 : Upper (D 6) (R 6) [10,48,192,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14498 : Route 9 := (fun mask => (mask,id))

def c14498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14498 : Upper (D 6) (R 6) [10,48,192,5,320,4] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5,320,4] 13 (by decide) (choices 1) [1,2,32] r14498 c14498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3272
  · exact u3273
  · exact u3274

def b14499 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 452, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 196 44 81 33 326 390 262), lower := (rows 11 50 196 44 81 33 64 128 256), losses := [] }

theorem u14499 : Upper (D 6) (R 6) [10,48,192,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14500 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 196 44 81 34 325 389 261), lower := (rows 11 50 196 44 81 34 64 128 256), losses := [] }

theorem u14500 : Upper (D 6) (R 6) [10,48,192,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14501 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 50 196 44 81 36 323 387 259), lower := (rows 11 50 196 44 81 36 64 128 256), losses := [] }

theorem u14501 : Upper (D 6) (R 6) [10,48,192,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14502 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 50 196 44 81 288 71 135 263), lower := (rows 11 50 196 44 81 288 64 128 256), losses := [] }

theorem u14502 : Upper (D 6) (R 6) [10,48,192,36,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14502 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14503 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 196 44 273 33 70 198 326), lower := (rows 11 50 196 44 273 33 64 128 256), losses := [] }

theorem u14503 : Upper (D 6) (R 6) [10,48,192,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14504 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 196 44 273 34 69 197 325), lower := (rows 11 50 196 44 273 34 64 128 256), losses := [] }

theorem u14504 : Upper (D 6) (R 6) [10,48,192,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14505 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 50 196 44 273 36 67 195 323), lower := (rows 11 50 196 44 273 36 64 128 256), losses := [] }

theorem u14505 : Upper (D 6) (R 6) [10,48,192,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14506 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 275, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 196 44 273 96 71 135 263), lower := (rows 11 50 196 44 273 96 64 128 256), losses := [] }

theorem u14506 : Upper (D 6) (R 6) [10,48,192,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14507 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 196 44 276 33 67 195 323), lower := (rows 11 50 196 44 276 33 64 128 256), losses := [] }

theorem u14507 : Upper (D 6) (R 6) [10,48,192,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14508 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 196 44 276 34 65 193 321), lower := (rows 11 50 196 44 276 34 64 128 256), losses := [] }

theorem u14508 : Upper (D 6) (R 6) [10,48,192,36,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14509 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 275, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 196 44 276 96 67 131 259), lower := (rows 11 50 196 44 276 96 64 128 256), losses := [] }

theorem u14509 : Upper (D 6) (R 6) [10,48,192,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14510 : Route 9 := (fun mask => (mask,id))

def c14510 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14510 : Upper (D 6) (R 6) [10,48,192,36,320,1] 13 := by
  apply FastRouting.sound _ _ [10,48,192,36,320,1] 13 (by decide) (choices 1) [1,2,4] r14510 c14510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3275
  · exact u3276
  · exact u3277

def b14511 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 196 44 336 34 69 133 261), lower := (rows 11 50 196 44 336 34 64 128 256), losses := [] }

theorem u14511 : Upper (D 6) (R 6) [10,48,192,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14512 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 50 196 44 336 36 67 131 259), lower := (rows 11 50 196 44 336 36 64 128 256), losses := [] }

theorem u14512 : Upper (D 6) (R 6) [10,48,192,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14513 : PairBound 9 := { available := 292, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 73 22 33 356 420 292), lower := (rows 11 50 196 73 22 33 64 128 256), losses := [] }

theorem u14513 : Upper (D 6) (R 6) [10,48,192,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14514 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 196 73 22 36 353 417 289), lower := (rows 11 50 196 73 22 36 64 128 256), losses := [] }

theorem u14514 : Upper (D 6) (R 6) [10,48,192,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14515 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 50 196 73 22 288 101 165 293), lower := (rows 11 50 196 73 22 288 64 128 256), losses := [] }

theorem u14515 : Upper (D 6) (R 6) [10,48,192,65,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14515 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14516 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 196 73 273 34 100 164 292), lower := (rows 11 50 196 73 273 34 64 128 256), losses := [] }

theorem u14516 : Upper (D 6) (R 6) [10,48,192,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14517 : Route 9 := (fun mask => (mask,id))

def c14517 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14517 : Upper (D 6) (R 6) [10,48,192,65,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,192,65,257,4] 13 (by decide) (choices 1) [2,4,32] r14517 c14517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3278
  · exact u3279
  · exact u3280

def b14518 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 73 274 33 100 164 292), lower := (rows 11 50 196 73 274 33 64 128 256), losses := [] }

theorem u14518 : Upper (D 6) (R 6) [10,48,192,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14519 : Route 9 := (fun mask => (mask,id))

def c14519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14519 : Upper (D 6) (R 6) [10,48,192,65,258,4] 13 := by
  apply FastRouting.sound _ _ [10,48,192,65,258,4] 13 (by decide) (choices 1) [1,4,32] r14519 c14519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3281
  · exact u3282
  · exact u3283

#print axioms u14519
end Delivery.IrregularNine14.P06
