import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0005

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4560 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 52 73 276 96 66 133 261), lower := (rows 11 162 52 73 276 96 66 128 256), losses := [] }

theorem u4560 : Upper (D 6) (R 6) [10,160,48,65,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4561 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 52 73 276 96 68 131 259), lower := (rows 11 162 52 73 276 96 68 128 256), losses := [] }

theorem u4561 : Upper (D 6) (R 6) [10,160,48,65,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4562 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 386, targets := 65 },{ cop := 0, region := 80, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 162 52 76 82 33 65 388 260), lower := (rows 11 162 52 76 82 33 65 128 256), losses := [] }

theorem u4562 : Upper (D 6) (R 6) [10,160,48,68,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4563 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 92, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 162 52 76 82 33 68 385 257), lower := (rows 11 162 52 76 82 33 68 128 256), losses := [] }

theorem u4563 : Upper (D 6) (R 6) [10,160,48,68,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4564 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 162 52 76 82 33 320 133 261), lower := (rows 11 162 52 76 82 33 320 128 256), losses := [] }

theorem u4564 : Upper (D 6) (R 6) [10,160,48,68,66,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4564 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4565 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 65 },{ cop := 4, region := 100, targets := 2 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 11 162 52 76 273 96 65 134 262), lower := (rows 11 162 52 76 273 96 65 128 256), losses := [] }

theorem u4565 : Upper (D 6) (R 6) [10,160,48,68,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4566 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 162 52 76 273 96 66 133 261), lower := (rows 11 162 52 76 273 96 66 128 256), losses := [{ target := 0, region := (rows 0 130 20 24 16 251 195 128 256), good := (rows 106 226 60 108 380 96 98 226 256) }] }

theorem u4566 : Upper (D 6) (R 6) [10,160,48,68,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4567 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 162 52 76 273 96 68 131 259), lower := (rows 11 162 52 76 273 96 68 128 256), losses := [] }

theorem u4567 : Upper (D 6) (R 6) [10,160,48,68,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4568 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,1),(4,0)], upper := (rows 11 162 52 76 274 33 65 196 324), lower := (rows 11 162 52 76 274 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 17 32 64 136 264), good := (rows 410 166 52 460 274 52 80 128 256) },{ target := 1, region := (rows 1 0 4 12 16 97 97 140 268), good := (rows 489 224 508 492 272 97 97 128 256) }] }

theorem u4568 : Upper (D 6) (R 6) [10,160,48,68,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4569 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 52 76 274 33 68 193 321), lower := (rows 11 162 52 76 274 33 68 128 256), losses := [] }

theorem u4569 : Upper (D 6) (R 6) [10,160,48,68,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4570 : Route 9 := (fun mask => (mask,id))

def c4570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4570 : Upper (D 6) (R 6) [10,160,48,68,258,64,1] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,258,64,1] 13 (by decide) (choices 1) [1,4] r4570 c4570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u340
  · exact u341

def b4571 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 162 52 76 274 96 68 129 257), lower := (rows 11 162 52 76 274 96 68 128 256), losses := [] }

theorem u4571 : Upper (D 6) (R 6) [10,160,48,68,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4572 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 11 162 52 76 276 33 65 194 322), lower := (rows 11 162 52 76 276 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 16 97 97 128 256), good := (rows 105 224 124 108 284 97 97 128 256) }] }

theorem u4572 : Upper (D 6) (R 6) [10,160,48,68,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4573 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(1,2),(4,5)], upper := (rows 11 162 52 76 276 33 66 193 321), lower := (rows 11 162 52 76 276 33 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 20 0 67 161 289), good := (rows 459 450 404 92 276 449 66 128 256) }] }

theorem u4573 : Upper (D 6) (R 6) [10,160,48,68,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4574 : Route 9 := (fun mask => (mask,id))

def c4574 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4574 : Upper (D 6) (R 6) [10,160,48,68,260,64,1] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,260,64,1] 13 (by decide) (choices 1) [1,2] r4574 c4574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u342
  · exact u343

def b4575 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 7, region := 98, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 162 52 76 276 96 66 129 257), lower := (rows 11 162 52 76 276 96 66 128 256), losses := [] }

theorem u4575 : Upper (D 6) (R 6) [10,160,48,68,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4576 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 65 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,0),(1,6)], upper := (rows 11 162 52 76 336 33 65 134 262), lower := (rows 11 162 52 76 336 33 65 128 256), losses := [] }

theorem u4576 : Upper (D 6) (R 6) [10,160,48,68,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4577 : Route 9 := (fun mask => (mask,id))

def c4577 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4577 : Upper (D 6) (R 6) [10,160,48,68,320,1,2] 13 := by
  apply FastRouting.sound _ _ [10,160,48,68,320,1,2] 13 (by decide) (choices 1) [1,4] r4577 c4577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u344
  · exact u345

def b4578 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 52 76 336 33 68 131 259), lower := (rows 11 162 52 76 336 33 68 128 256), losses := [] }

theorem u4578 : Upper (D 6) (R 6) [10,160,48,68,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4579 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 7, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 162 52 265 21 96 66 196 324), lower := (rows 11 162 52 265 21 96 66 128 256), losses := [] }

theorem u4579 : Upper (D 6) (R 6) [10,160,48,257,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4580 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 395, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 52 265 21 96 68 194 322), lower := (rows 11 162 52 265 21 96 68 128 256), losses := [] }

theorem u4580 : Upper (D 6) (R 6) [10,160,48,257,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4581 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 162 52 268 82 33 65 196 324), lower := (rows 11 162 52 268 82 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 28 16 97 97 148 276), good := (rows 105 224 508 396 508 97 97 128 256) }] }

theorem u4581 : Upper (D 6) (R 6) [10,160,48,260,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4582 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(0,5),(2,0),(4,0)], upper := (rows 11 162 52 268 82 33 68 193 321), lower := (rows 11 162 52 268 82 33 68 128 256), losses := [{ target := 5, region := (rows 17 2 4 76 17 0 76 149 277), good := (rows 475 130 477 460 475 401 460 128 256) }] }

theorem u4582 : Upper (D 6) (R 6) [10,160,48,260,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4583 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 162 52 268 84 33 65 194 322), lower := (rows 11 162 52 268 84 33 65 128 256), losses := [] }

theorem u4583 : Upper (D 6) (R 6) [10,160,48,260,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4584 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 1 },{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 11 162 52 268 84 33 66 193 321), lower := (rows 11 162 52 268 84 33 66 128 256), losses := [] }

theorem u4584 : Upper (D 6) (R 6) [10,160,48,260,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4585 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 130, targets := 65 },{ cop := 0, region := 80, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 162 52 328 82 33 65 132 260), lower := (rows 11 162 52 328 82 33 65 128 256), losses := [] }

theorem u4585 : Upper (D 6) (R 6) [10,160,48,320,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4586 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(0,5),(2,0),(4,0)], upper := (rows 11 162 52 328 82 33 68 133 261), lower := (rows 11 162 52 328 82 33 68 128 256), losses := [{ target := 5, region := (rows 17 2 4 76 16 0 68 132 260), good := (rows 11 130 477 328 91 1 460 128 256) }] }

theorem u4586 : Upper (D 6) (R 6) [10,160,48,320,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4587 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 2, region := 130, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 162 52 328 84 33 65 134 262), lower := (rows 11 162 52 328 84 33 65 128 256), losses := [] }

theorem u4587 : Upper (D 6) (R 6) [10,160,48,320,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4588 : Route 9 := (fun mask => (mask,id))

def c4588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4588 : Upper (D 6) (R 6) [10,160,48,320,68,1,2] 13 := by
  apply FastRouting.sound _ _ [10,160,48,320,68,1,2] 13 (by decide) (choices 1) [1,4] r4588 c4588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u346
  · exact u347

def b4589 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 52 328 84 33 68 131 259), lower := (rows 11 162 52 328 84 33 68 128 256), losses := [] }

theorem u4589 : Upper (D 6) (R 6) [10,160,48,320,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4590 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 2, region := 312, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 162 69 25 276 96 66 164 292), lower := (rows 11 162 69 25 276 96 66 128 256), losses := [] }

theorem u4590 : Upper (D 6) (R 6) [10,160,65,17,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4591 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 130, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 25 276 96 68 162 290), lower := (rows 11 162 69 25 276 96 68 128 256), losses := [] }

theorem u4591 : Upper (D 6) (R 6) [10,160,65,17,260,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4592 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 11 162 69 25 276 96 96 134 262), lower := (rows 11 162 69 25 276 96 96 128 256), losses := [] }

theorem u4592 : Upper (D 6) (R 6) [10,160,65,17,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4593 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 312, targets := 2 },{ cop := 7, region := 98, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 11 162 69 28 273 96 66 164 292), lower := (rows 11 162 69 28 273 96 66 128 256), losses := [] }

theorem u4593 : Upper (D 6) (R 6) [10,160,65,20,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4594 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 130, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 28 273 96 68 162 290), lower := (rows 11 162 69 28 273 96 68 128 256), losses := [] }

theorem u4594 : Upper (D 6) (R 6) [10,160,65,20,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4595 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 108, targets := 2 },{ cop := 7, region := 98, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 162 69 28 273 96 96 134 262), lower := (rows 11 162 69 28 273 96 96 128 256), losses := [] }

theorem u4595 : Upper (D 6) (R 6) [10,160,65,20,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4596 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 69 28 274 33 68 224 352), lower := (rows 11 162 69 28 274 33 68 128 256), losses := [] }

theorem u4596 : Upper (D 6) (R 6) [10,160,65,20,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4597 : Route 9 := (fun mask => (mask,id))

def c4597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4597 : Upper (D 6) (R 6) [10,160,65,20,258,1,32] 13 := by
  apply FastRouting.sound _ _ [10,160,65,20,258,1,32] 13 (by decide) (choices 1) [4,64] r4597 c4597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u348
  · exact u349

def b4598 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 28 274 36 65 224 352), lower := (rows 11 162 69 28 274 36 65 128 256), losses := [] }

theorem u4598 : Upper (D 6) (R 6) [10,160,65,20,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4599 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 11 162 69 28 274 36 96 193 321), lower := (rows 11 162 69 28 274 36 96 128 256), losses := [{ target := 2, region := (rows 1 34 0 8 49 32 98 133 261), good := (rows 475 242 465 408 338 498 114 128 256) }] }

theorem u4599 : Upper (D 6) (R 6) [10,160,65,20,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4600 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 28 274 96 65 164 292), lower := (rows 11 162 69 28 274 96 65 128 256), losses := [] }

theorem u4600 : Upper (D 6) (R 6) [10,160,65,20,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4601 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 69 28 274 96 68 161 289), lower := (rows 11 162 69 28 274 96 68 128 256), losses := [] }

theorem u4601 : Upper (D 6) (R 6) [10,160,65,20,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4602 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 98, targets := 5 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(1,2),(2,1)], upper := (rows 11 162 69 28 274 96 96 133 261), lower := (rows 11 162 69 28 274 96 96 128 256), losses := [] }

theorem u4602 : Upper (D 6) (R 6) [10,160,65,20,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4603 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 312, targets := 2 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 162 69 28 304 33 66 196 324), lower := (rows 11 162 69 28 304 33 66 128 256), losses := [] }

theorem u4603 : Upper (D 6) (R 6) [10,160,65,20,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4604 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 434, targets := 4 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 11 162 69 28 304 33 68 194 322), lower := (rows 11 162 69 28 304 33 68 128 256), losses := [] }

theorem u4604 : Upper (D 6) (R 6) [10,160,65,20,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4605 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 28 304 36 65 194 322), lower := (rows 11 162 69 28 304 36 65 128 256), losses := [] }

theorem u4605 : Upper (D 6) (R 6) [10,160,65,20,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4606 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 312, targets := 2 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 162 69 28 304 36 66 193 321), lower := (rows 11 162 69 28 304 36 66 128 256), losses := [] }

theorem u4606 : Upper (D 6) (R 6) [10,160,65,20,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4607 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 28 304 96 65 134 262), lower := (rows 11 162 69 28 304 96 65 128 256), losses := [] }

theorem u4607 : Upper (D 6) (R 6) [10,160,65,20,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4608 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 312, targets := 2 },{ cop := 7, region := 98, targets := 1 }], pairs := [(1,0),(3,1),(4,1)], upper := (rows 11 162 69 28 304 96 66 133 261), lower := (rows 11 162 69 28 304 96 66 128 256), losses := [] }

theorem u4608 : Upper (D 6) (R 6) [10,160,65,20,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4609 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 434, targets := 4 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 11 162 69 28 304 96 68 131 259), lower := (rows 11 162 69 28 304 96 68 128 256), losses := [] }

theorem u4609 : Upper (D 6) (R 6) [10,160,65,20,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4610 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 312, targets := 2 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 11 162 69 28 336 33 66 164 292), lower := (rows 11 162 69 28 336 33 66 128 256), losses := [] }

theorem u4610 : Upper (D 6) (R 6) [10,160,65,20,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4611 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 69 28 336 33 68 162 290), lower := (rows 11 162 69 28 336 33 68 128 256), losses := [] }

theorem u4611 : Upper (D 6) (R 6) [10,160,65,20,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4612 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 162 69 28 336 33 96 134 262), lower := (rows 11 162 69 28 336 33 96 128 256), losses := [] }

theorem u4612 : Upper (D 6) (R 6) [10,160,65,20,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4613 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 69 28 336 36 65 162 290), lower := (rows 11 162 69 28 336 36 65 128 256), losses := [] }

theorem u4613 : Upper (D 6) (R 6) [10,160,65,20,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4614 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 312, targets := 2 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(3,1),(4,1)], upper := (rows 11 162 69 28 336 36 66 161 289), lower := (rows 11 162 69 28 336 36 66 128 256), losses := [] }

theorem u4614 : Upper (D 6) (R 6) [10,160,65,20,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4615 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 162 69 28 336 36 96 131 259), lower := (rows 11 162 69 28 336 36 96 128 256), losses := [] }

theorem u4615 : Upper (D 6) (R 6) [10,160,65,20,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4616 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 265 22 36 80 224 352), lower := (rows 11 162 69 265 22 36 80 128 256), losses := [] }

theorem u4616 : Upper (D 6) (R 6) [10,160,65,257,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4616 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4617 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 178, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 11 162 69 265 22 36 96 208 336), lower := (rows 11 162 69 265 22 36 96 128 256), losses := [] }

theorem u4617 : Upper (D 6) (R 6) [10,160,65,257,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4618 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 2, region := 178, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 69 265 22 96 68 176 304), lower := (rows 11 162 69 265 22 96 68 128 256), losses := [] }

theorem u4618 : Upper (D 6) (R 6) [10,160,65,257,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4619 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 265 22 96 80 164 292), lower := (rows 11 162 69 265 22 96 80 128 256), losses := [] }

theorem u4619 : Upper (D 6) (R 6) [10,160,65,257,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4619 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4619
end Delivery.IrregularNine14.P06
