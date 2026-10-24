import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0131

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b25440 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 50 133 76 22 96 323 387 259), lower := (rows 41 50 133 76 22 96 64 128 256), losses := [] }

theorem u25440 : Upper (D 6) (R 6) [40,48,129,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25441 : Route 9 := (fun mask => (mask,id))

def c25441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25441 : Upper (D 6) (R 6) [40,48,129,68,6,256] 13 := by
  apply FastRouting.sound _ _ [40,48,129,68,6,256] 13 (by decide) (choices 1) [1,2] r25441 c25441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7866
  · exact u7867

def b25442 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 50 133 76 81 34 326 390 262), lower := (rows 41 50 133 76 81 34 64 128 256), losses := [] }

theorem u25442 : Upper (D 6) (R 6) [40,48,129,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25443 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 133 76 81 36 322 386 258), lower := (rows 41 50 133 76 81 36 64 128 256), losses := [] }

theorem u25443 : Upper (D 6) (R 6) [40,48,129,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25444 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 41 50 133 76 81 288 70 134 262), lower := (rows 41 50 133 76 81 288 64 128 256), losses := [] }

theorem u25444 : Upper (D 6) (R 6) [40,48,129,68,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25444 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25445 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 50 133 76 82 33 326 390 262), lower := (rows 41 50 133 76 82 33 64 128 256), losses := [] }

theorem u25445 : Upper (D 6) (R 6) [40,48,129,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25446 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 50 133 76 82 34 325 389 261), lower := (rows 41 50 133 76 82 34 64 128 256), losses := [] }

theorem u25446 : Upper (D 6) (R 6) [40,48,129,68,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25447 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 50, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 41 50 133 76 82 36 323 387 259), lower := (rows 41 50 133 76 82 36 64 128 256), losses := [] }

theorem u25447 : Upper (D 6) (R 6) [40,48,129,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25448 : Route 9 := (fun mask => (mask,id))

def c25448 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25448 : Upper (D 6) (R 6) [40,48,129,68,66,256] 13 := by
  apply FastRouting.sound _ _ [40,48,129,68,66,256] 13 (by decide) (choices 1) [1,2,4] r25448 c25448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7868
  · exact u7869
  · exact u7870

def b25449 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 50 133 76 273 34 70 198 326), lower := (rows 41 50 133 76 273 34 64 128 256), losses := [] }

theorem u25449 : Upper (D 6) (R 6) [40,48,129,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25450 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 133 76 273 36 66 194 322), lower := (rows 41 50 133 76 273 36 64 128 256), losses := [] }

theorem u25450 : Upper (D 6) (R 6) [40,48,129,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25451 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 50 133 76 273 96 70 134 262), lower := (rows 41 50 133 76 273 96 64 128 256), losses := [] }

theorem u25451 : Upper (D 6) (R 6) [40,48,129,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25452 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 50 133 76 274 33 70 198 326), lower := (rows 41 50 133 76 274 33 64 128 256), losses := [] }

theorem u25452 : Upper (D 6) (R 6) [40,48,129,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25453 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 50, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 50 133 76 274 34 69 197 325), lower := (rows 41 50 133 76 274 34 64 128 256), losses := [] }

theorem u25453 : Upper (D 6) (R 6) [40,48,129,68,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25454 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 133 76 274 36 67 195 323), lower := (rows 41 50 133 76 274 36 64 128 256), losses := [] }

theorem u25454 : Upper (D 6) (R 6) [40,48,129,68,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25455 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 50 133 76 274 96 71 135 263), lower := (rows 41 50 133 76 274 96 64 128 256), losses := [] }

theorem u25455 : Upper (D 6) (R 6) [40,48,129,68,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25456 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 50 133 76 276 33 66 194 322), lower := (rows 41 50 133 76 276 33 64 128 256), losses := [] }

theorem u25456 : Upper (D 6) (R 6) [40,48,129,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25457 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 50 133 76 276 34 67 195 323), lower := (rows 41 50 133 76 276 34 64 128 256), losses := [] }

theorem u25457 : Upper (D 6) (R 6) [40,48,129,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25458 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 50 133 76 276 96 67 131 259), lower := (rows 41 50 133 76 276 96 64 128 256), losses := [] }

theorem u25458 : Upper (D 6) (R 6) [40,48,129,68,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25459 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 50 133 76 336 33 70 134 262), lower := (rows 41 50 133 76 336 33 64 128 256), losses := [] }

theorem u25459 : Upper (D 6) (R 6) [40,48,129,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25460 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 50 133 76 336 34 71 135 263), lower := (rows 41 50 133 76 336 34 64 128 256), losses := [] }

theorem u25460 : Upper (D 6) (R 6) [40,48,129,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25461 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 133 76 336 36 67 131 259), lower := (rows 41 50 133 76 336 36 64 128 256), losses := [] }

theorem u25461 : Upper (D 6) (R 6) [40,48,129,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25462 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 50 133 265 22 34 68 196 324), lower := (rows 41 50 133 265 22 34 64 128 256), losses := [] }

theorem u25462 : Upper (D 6) (R 6) [40,48,129,257,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25463 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 2, region := 50, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 50 133 265 22 36 66 194 322), lower := (rows 41 50 133 265 22 36 64 128 256), losses := [] }

theorem u25463 : Upper (D 6) (R 6) [40,48,129,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25464 : Route 9 := (fun mask => (mask,id))

def c25464 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25464 : Upper (D 6) (R 6) [40,48,129,257,6,64] 13 := by
  apply FastRouting.sound _ _ [40,48,129,257,6,64] 13 (by decide) (choices 1) [2,4] r25464 c25464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7871
  · exact u7872

def b25465 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 50 133 265 82 34 68 196 324), lower := (rows 41 50 133 265 82 34 64 128 256), losses := [] }

theorem u25465 : Upper (D 6) (R 6) [40,48,129,257,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25466 : Route 9 := (fun mask => (mask,id))

def c25466 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25466 : Upper (D 6) (R 6) [40,48,129,257,66,4] 13 := by
  apply FastRouting.sound _ _ [40,48,129,257,66,4] 13 (by decide) (choices 1) [2,4] r25466 c25466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7873
  · exact u7874

def b25467 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 50 133 265 82 96 70 134 262), lower := (rows 41 50 133 265 82 96 64 128 256), losses := [] }

theorem u25467 : Upper (D 6) (R 6) [40,48,129,257,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25468 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 50 133 265 84 34 70 198 326), lower := (rows 41 50 133 265 84 34 64 128 256), losses := [] }

theorem u25468 : Upper (D 6) (R 6) [40,48,129,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25469 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 2, region := 114, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 50 133 265 84 36 66 194 322), lower := (rows 41 50 133 265 84 36 64 128 256), losses := [] }

theorem u25469 : Upper (D 6) (R 6) [40,48,129,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25470 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 50 133 265 84 96 70 134 262), lower := (rows 41 50 133 265 84 96 64 128 256), losses := [] }

theorem u25470 : Upper (D 6) (R 6) [40,48,129,257,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25471 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 133 266 81 34 68 196 324), lower := (rows 41 50 133 266 81 34 64 128 256), losses := [] }

theorem u25471 : Upper (D 6) (R 6) [40,48,129,258,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25472 : Route 9 := (fun mask => (mask,id))

def c25472 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25472 : Upper (D 6) (R 6) [40,48,129,258,65,4] 13 := by
  apply FastRouting.sound _ _ [40,48,129,258,65,4] 13 (by decide) (choices 1) [2,4] r25472 c25472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7875
  · exact u7876

def b25473 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 50 133 266 81 96 70 134 262), lower := (rows 41 50 133 266 81 96 64 128 256), losses := [] }

theorem u25473 : Upper (D 6) (R 6) [40,48,129,258,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25474 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 50 133 266 84 33 70 198 326), lower := (rows 41 50 133 266 84 33 64 128 256), losses := [] }

theorem u25474 : Upper (D 6) (R 6) [40,48,129,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25475 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 50 133 266 84 34 69 197 325), lower := (rows 41 50 133 266 84 34 64 128 256), losses := [] }

theorem u25475 : Upper (D 6) (R 6) [40,48,129,258,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25476 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 41 50 133 266 84 36 67 195 323), lower := (rows 41 50 133 266 84 36 64 128 256), losses := [] }

theorem u25476 : Upper (D 6) (R 6) [40,48,129,258,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25477 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 50 133 266 84 96 71 135 263), lower := (rows 41 50 133 266 84 96 64 128 256), losses := [] }

theorem u25477 : Upper (D 6) (R 6) [40,48,129,258,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25478 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 41 50 133 268 22 33 66 194 322), lower := (rows 41 50 133 268 22 33 64 128 256), losses := [] }

theorem u25478 : Upper (D 6) (R 6) [40,48,129,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25479 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 50 133 268 22 34 65 193 321), lower := (rows 41 50 133 268 22 34 64 128 256), losses := [] }

theorem u25479 : Upper (D 6) (R 6) [40,48,129,260,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25480 : Route 9 := (fun mask => (mask,id))

def c25480 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25480 : Upper (D 6) (R 6) [40,48,129,260,6,64] 13 := by
  apply FastRouting.sound _ _ [40,48,129,260,6,64] 13 (by decide) (choices 1) [1,2] r25480 c25480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7877
  · exact u7878

def b25481 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 50 133 268 81 34 70 198 326), lower := (rows 41 50 133 268 81 34 64 128 256), losses := [] }

theorem u25481 : Upper (D 6) (R 6) [40,48,129,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25482 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 133 268 81 36 66 194 322), lower := (rows 41 50 133 268 81 36 64 128 256), losses := [] }

theorem u25482 : Upper (D 6) (R 6) [40,48,129,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25483 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 50 133 268 81 96 70 134 262), lower := (rows 41 50 133 268 81 96 64 128 256), losses := [] }

theorem u25483 : Upper (D 6) (R 6) [40,48,129,260,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25484 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 50 133 268 82 33 70 198 326), lower := (rows 41 50 133 268 82 33 64 128 256), losses := [] }

theorem u25484 : Upper (D 6) (R 6) [40,48,129,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25485 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 50 133 268 82 34 69 197 325), lower := (rows 41 50 133 268 82 34 64 128 256), losses := [] }

theorem u25485 : Upper (D 6) (R 6) [40,48,129,260,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25486 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 50 133 268 82 36 67 195 323), lower := (rows 41 50 133 268 82 36 64 128 256), losses := [] }

theorem u25486 : Upper (D 6) (R 6) [40,48,129,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25487 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 41 50 133 268 82 96 71 135 263), lower := (rows 41 50 133 268 82 96 64 128 256), losses := [] }

theorem u25487 : Upper (D 6) (R 6) [40,48,129,260,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25488 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 50 133 268 84 33 66 194 322), lower := (rows 41 50 133 268 84 33 64 128 256), losses := [] }

theorem u25488 : Upper (D 6) (R 6) [40,48,129,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25489 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 41 50 133 268 84 34 67 195 323), lower := (rows 41 50 133 268 84 34 64 128 256), losses := [] }

theorem u25489 : Upper (D 6) (R 6) [40,48,129,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25490 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 50 133 268 84 96 67 131 259), lower := (rows 41 50 133 268 84 96 64 128 256), losses := [] }

theorem u25490 : Upper (D 6) (R 6) [40,48,129,260,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25491 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 50 133 328 22 33 70 198 326), lower := (rows 41 50 133 328 22 33 64 128 256), losses := [] }

theorem u25491 : Upper (D 6) (R 6) [40,48,129,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25492 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 50 133 328 22 34 69 197 325), lower := (rows 41 50 133 328 22 34 64 128 256), losses := [] }

theorem u25492 : Upper (D 6) (R 6) [40,48,129,320,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25493 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 41 50 133 328 22 36 67 195 323), lower := (rows 41 50 133 328 22 36 64 128 256), losses := [] }

theorem u25493 : Upper (D 6) (R 6) [40,48,129,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25494 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 150, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 50 133 328 22 96 71 135 263), lower := (rows 41 50 133 328 22 96 64 128 256), losses := [] }

theorem u25494 : Upper (D 6) (R 6) [40,48,129,320,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25495 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 50 133 328 81 34 70 134 262), lower := (rows 41 50 133 328 81 34 64 128 256), losses := [] }

theorem u25495 : Upper (D 6) (R 6) [40,48,129,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25496 : Route 9 := (fun mask => (mask,id))

def c25496 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25496 : Upper (D 6) (R 6) [40,48,129,320,65,4] 13 := by
  apply FastRouting.sound _ _ [40,48,129,320,65,4] 13 (by decide) (choices 1) [2,4] r25496 c25496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7879
  · exact u7880

def b25497 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 41 50 133 328 82 33 70 134 262), lower := (rows 41 50 133 328 82 33 64 128 256), losses := [] }

theorem u25497 : Upper (D 6) (R 6) [40,48,129,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b25498 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 50 133 328 82 34 69 133 261), lower := (rows 41 50 133 328 82 34 64 128 256), losses := [] }

theorem u25498 : Upper (D 6) (R 6) [40,48,129,320,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b25498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r25499 : Route 9 := (fun mask => (mask,id))

def c25499 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25499 : Upper (D 6) (R 6) [40,48,129,320,66,4] 13 := by
  apply FastRouting.sound _ _ [40,48,129,320,66,4] 13 (by decide) (choices 1) [1,2,4] r25499 c25499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7881
  · exact u7882
  · exact u7883

#print axioms u25499
end Delivery.IrregularNine14.P06
