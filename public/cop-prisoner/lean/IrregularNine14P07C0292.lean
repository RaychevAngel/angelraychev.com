import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0072

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17520 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 2, region := 200, targets := 1 }], pairs := [(1,6),(2,6),(2,7),(3,0)], upper := (rows 13 274 38 200 81 33 226 162 418), lower := (rows 13 274 38 200 81 33 64 128 256), losses := [{ target := 7, region := (rows 1 2 6 8 16 49 64 0 256), good := (rows 45 310 38 72 113 33 64 0 256) }] }

theorem u17520 : Upper (D 7) (R 7) [12,272,34,192,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17521 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 274 38 200 81 34 225 161 417), lower := (rows 13 274 38 200 81 34 64 128 256), losses := [] }

theorem u17521 : Upper (D 7) (R 7) [12,272,34,192,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17522 : Route 9 := (fun mask => (mask,id))

def c17522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17522 : Upper (D 7) (R 7) [12,272,34,192,65,128] 13 := by
  apply FastRouting.sound _ _ [12,272,34,192,65,128] 13 (by decide) (choices 1) [1,2,32] r17522 c17522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4325
  · exact u4326
  · exact u4327

def r17523 : Route 9 := (fun mask => (mask,id))

def c17523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17523 : Upper (D 7) (R 7) [12,272,34,192,66,1] 13 := by
  apply FastRouting.sound _ _ [12,272,34,192,66,1] 13 (by decide) (choices 1) [1,32,128] r17523 c17523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4328
  · exact u4329
  · exact u4330

def r17524 : Route 9 := (fun mask => (mask,id))

def c17524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17524 : Upper (D 7) (R 7) [12,272,34,192,66,128] 13 := by
  apply FastRouting.sound _ _ [12,272,34,192,66,128] 13 (by decide) (choices 1) [1,32] r17524 c17524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4331
  · exact u4332

def r17525 : Route 9 := (fun mask => (mask,id))

def c17525 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17525 : Upper (D 7) (R 7) [12,272,34,192,96,1] 13 := by
  apply FastRouting.sound _ _ [12,272,34,192,96,1] 13 (by decide) (choices 1) [1,2,128] r17525 c17525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4333
  · exact u4334
  · exact u4335

def b17526 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 36, targets := 193 },{ cop := 2, region := 201, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(2,7)], upper := (rows 13 274 38 200 112 34 193 129 385), lower := (rows 13 274 38 200 112 34 64 128 256), losses := [] }

theorem u17526 : Upper (D 7) (R 7) [12,272,34,192,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17527 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 201, targets := 32 },{ cop := 3, region := 48, targets := 3 }], pairs := [(0,5),(3,5),(4,0),(4,1)], upper := (rows 13 274 38 200 112 160 67 131 259), lower := (rows 13 274 38 200 112 160 64 128 256), losses := [] }

theorem u17527 : Upper (D 7) (R 7) [12,272,34,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17528 : Route 9 := (fun mask => (mask,id))

def c17528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17528 : Upper (D 7) (R 7) [12,272,96,160,3,1] 13 := by
  apply FastRouting.sound _ _ [12,272,96,160,3,1] 13 (by decide) (choices 1) [2,128] r17528 c17528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4336
  · exact u4337

def b17529 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 205, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 13 274 100 168 19 34 193 193 449), lower := (rows 13 274 100 168 19 34 64 128 256), losses := [] }

theorem u17529 : Upper (D 7) (R 7) [12,272,96,160,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17530 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 13 274 100 168 19 96 195 131 387), lower := (rows 13 274 100 168 19 96 64 128 256), losses := [] }

theorem u17530 : Upper (D 7) (R 7) [12,272,96,160,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17531 : Route 9 := (fun mask => (mask,id))

def c17531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17531 : Upper (D 7) (R 7) [12,272,96,160,66,1] 13 := by
  apply FastRouting.sound _ _ [12,272,96,160,66,1] 13 (by decide) (choices 1) [1,2,128] r17531 c17531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4338
  · exact u4339
  · exact u4340

def b17532 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 205, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 13 274 100 168 82 34 193 129 385), lower := (rows 13 274 100 168 82 34 64 128 256), losses := [] }

theorem u17532 : Upper (D 7) (R 7) [12,272,96,160,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17533 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 274 100 168 82 160 67 131 259), lower := (rows 13 274 100 168 82 160 64 128 256), losses := [] }

theorem u17533 : Upper (D 7) (R 7) [12,272,96,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17534 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 13 274 100 168 208 33 67 131 259), lower := (rows 13 274 100 168 208 33 64 128 256), losses := [] }

theorem u17534 : Upper (D 7) (R 7) [12,272,96,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17535 : Route 9 := (fun mask => (mask,id))

def c17535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17535 : Upper (D 7) (R 7) [12,272,96,160,192,2] 13 := by
  apply FastRouting.sound _ _ [12,272,96,160,192,2] 13 (by decide) (choices 1) [1,2] r17535 c17535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4341
  · exact u4342

def b17536 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 7 25 112 34 192 192 448), lower := (rows 13 290 7 25 112 34 64 128 256), losses := [] }

theorem u17536 : Upper (D 7) (R 7) [12,288,3,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17537 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(3,6)], upper := (rows 13 290 7 25 112 96 194 130 386), lower := (rows 13 290 7 25 112 96 64 128 256), losses := [] }

theorem u17537 : Upper (D 7) (R 7) [12,288,3,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17538 : Route 9 := (fun mask => (mask,id))

def c17538 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17538 : Upper (D 7) (R 7) [12,288,3,17,96,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,17,96,128] 13 (by decide) (choices 1) [2,128] r17538 c17538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4343
  · exact u4344

def b17539 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 7 25 208 34 224 224 480), lower := (rows 13 290 7 25 208 34 64 128 256), losses := [] }

theorem u17539 : Upper (D 7) (R 7) [12,288,3,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17540 : Route 9 := (fun mask => (mask,id))

def c17540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17540 : Upper (D 7) (R 7) [12,288,3,17,192,64] 13 := by
  apply FastRouting.sound _ _ [12,288,3,17,192,64] 13 (by decide) (choices 1) [2,32,128] r17540 c17540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4345
  · exact u4346
  · exact u4347

def b17541 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 13 290 7 56 81 34 192 192 448), lower := (rows 13 290 7 56 81 34 64 128 256), losses := [] }

theorem u17541 : Upper (D 7) (R 7) [12,288,3,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17542 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 418, targets := 1 }], pairs := [(0,6),(1,0),(1,6),(2,6)], upper := (rows 13 290 7 56 81 96 194 130 386), lower := (rows 13 290 7 56 81 96 64 128 256), losses := [] }

theorem u17542 : Upper (D 7) (R 7) [12,288,3,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17543 : Route 9 := (fun mask => (mask,id))

def c17543 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17543 : Upper (D 7) (R 7) [12,288,3,48,65,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,48,65,128] 13 (by decide) (choices 1) [2,128] r17543 c17543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4348
  · exact u4349

def b17544 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 290 7 56 82 33 192 192 448), lower := (rows 13 290 7 56 82 33 64 128 256), losses := [] }

theorem u17544 : Upper (D 7) (R 7) [12,288,3,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17545 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 45, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(2,6)], upper := (rows 13 290 7 56 82 96 193 129 385), lower := (rows 13 290 7 56 82 96 64 128 256), losses := [] }

theorem u17545 : Upper (D 7) (R 7) [12,288,3,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17546 : Route 9 := (fun mask => (mask,id))

def c17546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17546 : Upper (D 7) (R 7) [12,288,3,48,66,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,48,66,128] 13 (by decide) (choices 1) [1,128] r17546 c17546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4350
  · exact u4351

def b17547 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 290 7 56 208 33 194 194 450), lower := (rows 13 290 7 56 208 33 64 128 256), losses := [] }

theorem u17547 : Upper (D 7) (R 7) [12,288,3,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17548 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 290 7 56 208 34 193 193 449), lower := (rows 13 290 7 56 208 34 64 128 256), losses := [] }

theorem u17548 : Upper (D 7) (R 7) [12,288,3,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17549 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 391, targets := 64 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0)], upper := (rows 13 290 7 56 208 96 195 131 387), lower := (rows 13 290 7 56 208 96 64 128 256), losses := [] }

theorem u17549 : Upper (D 7) (R 7) [12,288,3,48,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17550 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 7 73 112 34 208 144 400), lower := (rows 13 290 7 73 112 34 64 128 256), losses := [] }

theorem u17550 : Upper (D 7) (R 7) [12,288,3,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17551 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 290 7 73 112 48 194 130 386), lower := (rows 13 290 7 73 112 48 64 128 256), losses := [] }

theorem u17551 : Upper (D 7) (R 7) [12,288,3,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17551 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17552 : Route 9 := (fun mask => (mask,id))

def c17552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17552 : Upper (D 7) (R 7) [12,288,3,65,96,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,65,96,128] 13 (by decide) (choices 1) [2,16,128] r17552 c17552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4352
  · exact u4353
  · exact u4354

def b17553 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 13 290 7 73 146 48 224 224 480), lower := (rows 13 290 7 73 146 48 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 16 48 114 178 306), good := (rows 13 480 461 73 496 496 64 128 256) }] }

theorem u17553 : Upper (D 7) (R 7) [12,288,3,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17553 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17554 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 290 7 73 146 96 240 176 432), lower := (rows 13 290 7 73 146 96 64 128 256), losses := [] }

theorem u17554 : Upper (D 7) (R 7) [12,288,3,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17555 : Route 9 := (fun mask => (mask,id))

def c17555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17555 : Upper (D 7) (R 7) [12,288,3,65,130,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,65,130,128] 13 (by decide) (choices 1) [16,32] r17555 c17555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4355
  · exact u4356

def b17556 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 7 73 176 34 208 208 464), lower := (rows 13 290 7 73 176 34 64 128 256), losses := [] }

theorem u17556 : Upper (D 7) (R 7) [12,288,3,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17556 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17557 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 205, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 290 7 73 176 48 194 194 450), lower := (rows 13 290 7 73 176 48 64 128 256), losses := [] }

theorem u17557 : Upper (D 7) (R 7) [12,288,3,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17557 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17558 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 290 7 73 176 96 210 146 402), lower := (rows 13 290 7 73 176 96 64 128 256), losses := [] }

theorem u17558 : Upper (D 7) (R 7) [12,288,3,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17559 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 7 73 176 160 82 210 338), lower := (rows 13 290 7 73 176 160 64 128 256), losses := [] }

theorem u17559 : Upper (D 7) (R 7) [12,288,3,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17560 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 290 7 73 208 34 240 176 432), lower := (rows 13 290 7 73 208 34 64 128 256), losses := [] }

theorem u17560 : Upper (D 7) (R 7) [12,288,3,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17561 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 13 290 7 73 208 48 226 162 418), lower := (rows 13 290 7 73 208 48 64 128 256), losses := [] }

theorem u17561 : Upper (D 7) (R 7) [12,288,3,65,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17561 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17562 : Route 9 := (fun mask => (mask,id))

def c17562 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17562 : Upper (D 7) (R 7) [12,288,3,65,192,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,65,192,128] 13 (by decide) (choices 1) [2,16,32] r17562 c17562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4357
  · exact u4358
  · exact u4359

def b17563 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 48, targets := 192 },{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 13 290 7 88 49 34 192 192 448), lower := (rows 13 290 7 88 49 34 64 128 256), losses := [] }

theorem u17563 : Upper (D 7) (R 7) [12,288,3,80,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17564 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 4, region := 390, targets := 64 }], pairs := [(1,0),(1,6),(2,6),(3,0)], upper := (rows 13 290 7 88 49 96 194 130 386), lower := (rows 13 290 7 88 49 96 64 128 256), losses := [] }

theorem u17564 : Upper (D 7) (R 7) [12,288,3,80,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17565 : Route 9 := (fun mask => (mask,id))

def c17565 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17565 : Upper (D 7) (R 7) [12,288,3,80,33,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80,33,128] 13 (by decide) (choices 1) [2,128] r17565 c17565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4360
  · exact u4361

def b17566 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 8, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 13 290 7 88 145 34 224 224 480), lower := (rows 13 290 7 88 145 34 64 128 256), losses := [] }

theorem u17566 : Upper (D 7) (R 7) [12,288,3,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17567 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 5, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,6)], upper := (rows 13 290 7 88 145 96 226 162 418), lower := (rows 13 290 7 88 145 96 64 128 256), losses := [{ target := 6, region := (rows 1 34 4 8 20 32 0 162 290), good := (rows 29 418 407 24 145 418 0 128 256) }] }

theorem u17567 : Upper (D 7) (R 7) [12,288,3,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17568 : Route 9 := (fun mask => (mask,id))

def c17568 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17568 : Upper (D 7) (R 7) [12,288,3,80,129,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80,129,128] 13 (by decide) (choices 1) [2,32] r17568 c17568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4362
  · exact u4363

def b17569 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 13 290 7 88 146 33 224 224 480), lower := (rows 13 290 7 88 146 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 103 167 295), good := (rows 493 480 485 88 472 481 64 128 256) }] }

theorem u17569 : Upper (D 7) (R 7) [12,288,3,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17570 : Route 9 := (fun mask => (mask,id))

def c17570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17570 : Upper (D 7) (R 7) [12,288,3,80,130,64] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80,130,64] 13 (by decide) (choices 1) [1,32,128] r17570 c17570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4364
  · exact u4365
  · exact u4366

def r17571 : Route 9 := (fun mask => (mask,id))

def c17571 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17571 : Upper (D 7) (R 7) [12,288,3,80,130,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80,130,128] 13 (by decide) (choices 1) [1,32] r17571 c17571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4367
  · exact u4368

def r17572 : Route 9 := (fun mask => (mask,id))

def c17572 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17572 : Upper (D 7) (R 7) [12,288,3,80,160,1] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80,160,1] 13 (by decide) (choices 1) [2,128] r17572 c17572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4369
  · exact u4370

def r17573 : Route 9 := (fun mask => (mask,id))

def c17573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17573 : Upper (D 7) (R 7) [12,288,3,80,160,2] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80,160,2] 13 (by decide) (choices 1) [1,128] r17573 c17573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4371
  · exact u4372

def r17574 : Route 9 := (fun mask => (mask,id))

def c17574 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17574 : Upper (D 7) (R 7) [12,288,3,80,160,64] 13 := by
  apply FastRouting.sound _ _ [12,288,3,80,160,64] 13 (by decide) (choices 1) [1,2,128] r17574 c17574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4373
  · exact u4374
  · exact u4375

def b17575 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 290 7 88 176 160 67 195 323), lower := (rows 13 290 7 88 176 160 64 128 256), losses := [] }

theorem u17575 : Upper (D 7) (R 7) [12,288,3,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17575 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17576 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 290 7 104 82 33 208 144 400), lower := (rows 13 290 7 104 82 33 64 128 256), losses := [] }

theorem u17576 : Upper (D 7) (R 7) [12,288,3,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17577 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 13 290 7 104 82 48 193 129 385), lower := (rows 13 290 7 104 82 48 64 128 256), losses := [] }

theorem u17577 : Upper (D 7) (R 7) [12,288,3,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17577 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17578 : Route 9 := (fun mask => (mask,id))

def c17578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17578 : Upper (D 7) (R 7) [12,288,3,96,66,128] 13 := by
  apply FastRouting.sound _ _ [12,288,3,96,66,128] 13 (by decide) (choices 1) [1,16,128] r17578 c17578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4376
  · exact u4377
  · exact u4378

def b17579 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 290 7 104 145 34 208 208 464), lower := (rows 13 290 7 104 145 34 64 128 256), losses := [] }

theorem u17579 : Upper (D 7) (R 7) [12,288,3,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17579
end Delivery.IrregularNine14.P07
