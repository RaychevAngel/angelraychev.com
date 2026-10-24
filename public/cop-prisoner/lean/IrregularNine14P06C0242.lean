import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0054
import IrregularNine14P06C0055

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14520 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 73 276 33 102 166 294), lower := (rows 11 50 196 73 276 33 64 128 256), losses := [] }

theorem u14520 : Upper (D 6) (R 6) [10,48,192,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14520 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14521 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 196 73 276 34 101 165 293), lower := (rows 11 50 196 73 276 34 64 128 256), losses := [] }

theorem u14521 : Upper (D 6) (R 6) [10,48,192,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14522 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 196 73 276 36 99 163 291), lower := (rows 11 50 196 73 276 36 64 128 256), losses := [] }

theorem u14522 : Upper (D 6) (R 6) [10,48,192,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14523 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 196 104 273 33 70 134 262), lower := (rows 11 50 196 104 273 33 64 128 256), losses := [] }

theorem u14523 : Upper (D 6) (R 6) [10,48,192,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14524 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 196 104 273 34 69 133 261), lower := (rows 11 50 196 104 273 34 64 128 256), losses := [] }

theorem u14524 : Upper (D 6) (R 6) [10,48,192,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14525 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 50 196 104 273 36 71 135 263), lower := (rows 11 50 196 104 273 36 64 128 256), losses := [] }

theorem u14525 : Upper (D 6) (R 6) [10,48,192,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14526 : Route 9 := (fun mask => (mask,id))

def c14526 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14526 : Upper (D 6) (R 6) [10,48,192,96,260,1] 13 := by
  apply FastRouting.sound _ _ [10,48,192,96,260,1] 13 (by decide) (choices 1) [1,2,4] r14526 c14526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3284
  · exact u3285
  · exact u3286

def b14527 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 196 104 276 34 69 133 261), lower := (rows 11 50 196 104 276 34 64 128 256), losses := [] }

theorem u14527 : Upper (D 6) (R 6) [10,48,192,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14528 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 196 104 276 36 67 131 259), lower := (rows 11 50 196 104 276 36 64 128 256), losses := [] }

theorem u14528 : Upper (D 6) (R 6) [10,48,192,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14528 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14529 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 196 265 21 34 100 228 356), lower := (rows 11 50 196 265 21 34 64 128 256), losses := [] }

theorem u14529 : Upper (D 6) (R 6) [10,48,192,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14530 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 196 265 21 36 98 226 354), lower := (rows 11 50 196 265 21 36 64 128 256), losses := [] }

theorem u14530 : Upper (D 6) (R 6) [10,48,192,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14531 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 196 265 21 96 102 166 294), lower := (rows 11 50 196 265 21 96 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 100 64 128 256), good := (rows 11 50 224 265 51 96 96 128 256) }] }

theorem u14531 : Upper (D 6) (R 6) [10,48,192,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14532 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 265 22 33 100 228 356), lower := (rows 11 50 196 265 22 33 64 128 256), losses := [] }

theorem u14532 : Upper (D 6) (R 6) [10,48,192,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14533 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 196 265 22 36 97 225 353), lower := (rows 11 50 196 265 22 36 64 128 256), losses := [] }

theorem u14533 : Upper (D 6) (R 6) [10,48,192,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14534 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 196 265 22 96 101 165 293), lower := (rows 11 50 196 265 22 96 64 128 256), losses := [] }

theorem u14534 : Upper (D 6) (R 6) [10,48,192,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14535 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 196 265 81 34 100 164 292), lower := (rows 11 50 196 265 81 34 64 128 256), losses := [] }

theorem u14535 : Upper (D 6) (R 6) [10,48,192,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14536 : Route 9 := (fun mask => (mask,id))

def c14536 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14536 : Upper (D 6) (R 6) [10,48,192,257,65,4] 13 := by
  apply FastRouting.sound _ _ [10,48,192,257,65,4] 13 (by decide) (choices 1) [2,4,32] r14536 c14536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3287
  · exact u3288
  · exact u3289

def b14537 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 265 82 33 100 164 292), lower := (rows 11 50 196 265 82 33 64 128 256), losses := [] }

theorem u14537 : Upper (D 6) (R 6) [10,48,192,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14538 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 196 265 82 36 101 165 293), lower := (rows 11 50 196 265 82 36 64 128 256), losses := [] }

theorem u14538 : Upper (D 6) (R 6) [10,48,192,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14539 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 196 268 21 33 98 226 354), lower := (rows 11 50 196 268 21 33 64 128 256), losses := [] }

theorem u14539 : Upper (D 6) (R 6) [10,48,192,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14539 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14540 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 196 268 21 34 97 225 353), lower := (rows 11 50 196 268 21 34 64 128 256), losses := [] }

theorem u14540 : Upper (D 6) (R 6) [10,48,192,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14541 : Route 9 := (fun mask => (mask,id))

def c14541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14541 : Upper (D 6) (R 6) [10,48,192,260,5,64] 13 := by
  apply FastRouting.sound _ _ [10,48,192,260,5,64] 13 (by decide) (choices 1) [1,2,32] r14541 c14541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3290
  · exact u3291
  · exact u3292

def b14542 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 196 268 22 33 97 225 353), lower := (rows 11 50 196 268 22 33 64 128 256), losses := [] }

theorem u14542 : Upper (D 6) (R 6) [10,48,192,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14543 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 196 268 22 96 97 161 289), lower := (rows 11 50 196 268 22 96 64 128 256), losses := [] }

theorem u14543 : Upper (D 6) (R 6) [10,48,192,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14544 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 196 268 81 33 102 166 294), lower := (rows 11 50 196 268 81 33 64 128 256), losses := [] }

theorem u14544 : Upper (D 6) (R 6) [10,48,192,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14545 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 196 268 81 34 101 165 293), lower := (rows 11 50 196 268 81 34 64 128 256), losses := [] }

theorem u14545 : Upper (D 6) (R 6) [10,48,192,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14546 : Route 9 := (fun mask => (mask,id))

def c14546 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14546 : Upper (D 6) (R 6) [10,48,192,260,65,4] 13 := by
  apply FastRouting.sound _ _ [10,48,192,260,65,4] 13 (by decide) (choices 1) [1,2,32] r14546 c14546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3293
  · exact u3294
  · exact u3295

def r14547 : Route 9 := (fun mask => (mask,id))

def c14547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14547 : Upper (D 6) (R 6) [10,48,192,260,66,1] 13 := by
  apply FastRouting.sound _ _ [10,48,192,260,66,1] 13 (by decide) (choices 1) [1,4,32] r14547 c14547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3296
  · exact u3297
  · exact u3298

def b14548 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 196 268 82 36 97 161 289), lower := (rows 11 50 196 268 82 36 64 128 256), losses := [] }

theorem u14548 : Upper (D 6) (R 6) [10,48,192,260,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14549 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 196 296 21 33 70 198 326), lower := (rows 11 50 196 296 21 33 64 128 256), losses := [] }

theorem u14549 : Upper (D 6) (R 6) [10,48,192,288,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14550 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 196 296 21 34 69 197 325), lower := (rows 11 50 196 296 21 34 64 128 256), losses := [] }

theorem u14550 : Upper (D 6) (R 6) [10,48,192,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14551 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 196 296 21 36 67 195 323), lower := (rows 11 50 196 296 21 36 64 128 256), losses := [] }

theorem u14551 : Upper (D 6) (R 6) [10,48,192,288,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14552 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 50 196 296 21 96 71 135 263), lower := (rows 11 50 196 296 21 96 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 100 64 128 256), good := (rows 10 50 228 296 54 96 96 128 256) }] }

theorem u14552 : Upper (D 6) (R 6) [10,48,192,288,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14553 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 196 296 81 33 70 134 262), lower := (rows 11 50 196 296 81 33 64 128 256), losses := [] }

theorem u14553 : Upper (D 6) (R 6) [10,48,192,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14554 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 196 296 81 34 69 133 261), lower := (rows 11 50 196 296 81 34 64 128 256), losses := [] }

theorem u14554 : Upper (D 6) (R 6) [10,48,192,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14555 : Route 9 := (fun mask => (mask,id))

def c14555 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14555 : Upper (D 6) (R 6) [10,48,192,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,48,192,288,65,4] 13 (by decide) (choices 1) [1,2,4] r14555 c14555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3299
  · exact u3300
  · exact u3301

def b14556 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 196 328 21 33 102 166 294), lower := (rows 11 50 196 328 21 33 64 128 256), losses := [] }

theorem u14556 : Upper (D 6) (R 6) [10,48,192,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14557 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 34, targets := 5 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 196 328 21 34 101 165 293), lower := (rows 11 50 196 328 21 34 64 128 256), losses := [] }

theorem u14557 : Upper (D 6) (R 6) [10,48,192,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14558 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 196 328 21 36 99 163 291), lower := (rows 11 50 196 328 21 36 64 128 256), losses := [] }

theorem u14558 : Upper (D 6) (R 6) [10,48,192,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14559 : Route 9 := (fun mask => (mask,id))

def c14559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14559 : Upper (D 6) (R 6) [10,48,192,320,6,1] 13 := by
  apply FastRouting.sound _ _ [10,48,192,320,6,1] 13 (by decide) (choices 1) [1,4,32] r14559 c14559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3302
  · exact u3303
  · exact u3304

def b14560 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 196 328 22 36 97 161 289), lower := (rows 11 50 196 328 22 36 64 128 256), losses := [] }

theorem u14560 : Upper (D 6) (R 6) [10,48,192,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14561 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 388 13 81 34 100 228 356), lower := (rows 11 50 388 13 81 34 64 128 256), losses := [] }

theorem u14561 : Upper (D 6) (R 6) [10,48,384,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14562 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 11 50 388 13 81 36 98 226 354), lower := (rows 11 50 388 13 81 36 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 17 32 66 130 258), good := (rows 475 498 384 25 81 32 64 128 256) }] }

theorem u14562 : Upper (D 6) (R 6) [10,48,384,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14563 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 388 13 81 96 102 166 294), lower := (rows 11 50 388 13 81 96 64 128 256), losses := [] }

theorem u14563 : Upper (D 6) (R 6) [10,48,384,5,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14564 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 388 13 82 33 100 228 356), lower := (rows 11 50 388 13 82 33 64 128 256), losses := [] }

theorem u14564 : Upper (D 6) (R 6) [10,48,384,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14565 : Route 9 := (fun mask => (mask,id))

def c14565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14565 : Upper (D 6) (R 6) [10,48,384,5,66,4] 13 := by
  apply FastRouting.sound _ _ [10,48,384,5,66,4] 13 (by decide) (choices 1) [1,32] r14565 c14565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3305
  · exact u3306

def b14566 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 388 13 82 96 101 165 293), lower := (rows 11 50 388 13 82 96 64 128 256), losses := [] }

theorem u14566 : Upper (D 6) (R 6) [10,48,384,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14567 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 388 13 84 33 98 226 354), lower := (rows 11 50 388 13 84 33 64 128 256), losses := [] }

theorem u14567 : Upper (D 6) (R 6) [10,48,384,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14568 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 388 13 84 34 97 225 353), lower := (rows 11 50 388 13 84 34 64 128 256), losses := [] }

theorem u14568 : Upper (D 6) (R 6) [10,48,384,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14569 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 388 13 84 96 99 163 291), lower := (rows 11 50 388 13 84 96 64 128 256), losses := [] }

theorem u14569 : Upper (D 6) (R 6) [10,48,384,5,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14570 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 452, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 388 44 81 33 70 198 326), lower := (rows 11 50 388 44 81 33 64 128 256), losses := [] }

theorem u14570 : Upper (D 6) (R 6) [10,48,384,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14571 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 388 44 81 34 69 197 325), lower := (rows 11 50 388 44 81 34 64 128 256), losses := [] }

theorem u14571 : Upper (D 6) (R 6) [10,48,384,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14572 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 50 388 44 81 36 67 195 323), lower := (rows 11 50 388 44 81 36 64 128 256), losses := [] }

theorem u14572 : Upper (D 6) (R 6) [10,48,384,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14573 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 388 44 81 96 71 135 263), lower := (rows 11 50 388 44 81 96 64 128 256), losses := [] }

theorem u14573 : Upper (D 6) (R 6) [10,48,384,36,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14574 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 388 44 84 33 67 195 323), lower := (rows 11 50 388 44 84 33 64 128 256), losses := [] }

theorem u14574 : Upper (D 6) (R 6) [10,48,384,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14575 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 388 44 84 34 65 193 321), lower := (rows 11 50 388 44 84 34 64 128 256), losses := [] }

theorem u14575 : Upper (D 6) (R 6) [10,48,384,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14576 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 388 44 84 96 67 131 259), lower := (rows 11 50 388 44 84 96 64 128 256), losses := [] }

theorem u14576 : Upper (D 6) (R 6) [10,48,384,36,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14577 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 388 73 21 34 100 228 356), lower := (rows 11 50 388 73 21 34 64 128 256), losses := [] }

theorem u14577 : Upper (D 6) (R 6) [10,48,384,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14578 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 388 73 21 36 98 226 354), lower := (rows 11 50 388 73 21 36 64 128 256), losses := [] }

theorem u14578 : Upper (D 6) (R 6) [10,48,384,65,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14579 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 1, region := 388, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 50 388 73 21 96 102 166 294), lower := (rows 11 50 388 73 21 96 64 128 256), losses := [] }

theorem u14579 : Upper (D 6) (R 6) [10,48,384,65,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14579
end Delivery.IrregularNine14.P06
