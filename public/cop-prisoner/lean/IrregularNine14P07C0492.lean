import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0188
import IrregularNine14P07C0189

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29520 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 290 13 28 146 33 194 194 450), lower := (rows 97 290 13 28 146 33 64 128 256), losses := [] }

theorem u29520 : Upper (D 7) (R 7) [96,288,9,20,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29521 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(1,0),(1,6),(1,7)], upper := (rows 97 290 13 28 146 34 193 193 449), lower := (rows 97 290 13 28 146 34 64 128 256), losses := [] }

theorem u29521 : Upper (D 7) (R 7) [96,288,9,20,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29522 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 13 28 146 96 195 131 387), lower := (rows 97 290 13 28 146 96 64 128 256), losses := [] }

theorem u29522 : Upper (D 7) (R 7) [96,288,9,20,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29523 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 97 290 13 28 146 160 67 195 323), lower := (rows 97 290 13 28 146 160 64 128 256), losses := [{ target := 7, region := (rows 35 35 20 24 16 32 119 0 311), good := (rows 355 355 335 348 351 355 64 0 256) }] }

theorem u29523 : Upper (D 7) (R 7) [96,288,9,20,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29524 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 290 13 28 208 33 194 130 386), lower := (rows 97 290 13 28 208 33 64 128 256), losses := [] }

theorem u29524 : Upper (D 7) (R 7) [96,288,9,20,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29525 : Route 9 := (fun mask => (mask,id))

def c29525 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29525 : Upper (D 7) (R 7) [96,288,9,20,192,2] 13 := by
  apply FastRouting.sound _ _ [96,288,9,20,192,2] 13 (by decide) (choices 1) [1,2,128] r29525 c29525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11332
  · exact u11333
  · exact u11334

def b29526 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 290 13 28 208 160 67 131 259), lower := (rows 97 290 13 28 208 160 64 128 256), losses := [] }

theorem u29526 : Upper (D 7) (R 7) [96,288,9,20,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29527 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 2, region := 434, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(4,7)], upper := (rows 97 290 13 74 22 33 208 144 400), lower := (rows 97 290 13 74 22 33 64 128 256), losses := [] }

theorem u29527 : Upper (D 7) (R 7) [96,288,9,66,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29528 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 53, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 290 13 74 22 48 193 129 385), lower := (rows 97 290 13 74 22 48 64 128 256), losses := [] }

theorem u29528 : Upper (D 7) (R 7) [96,288,9,66,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29528 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29529 : Route 9 := (fun mask => (mask,id))

def c29529 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29529 : Upper (D 7) (R 7) [96,288,9,66,6,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,66,6,128] 13 (by decide) (choices 1) [1,16,128] r29529 c29529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11335
  · exact u11336
  · exact u11337

def b29530 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 144, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 13 74 145 34 212 148 404), lower := (rows 97 290 13 74 145 34 64 128 256), losses := [] }

theorem u29530 : Upper (D 7) (R 7) [96,288,9,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29531 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 290 13 74 145 36 210 146 402), lower := (rows 97 290 13 74 145 36 64 128 256), losses := [] }

theorem u29531 : Upper (D 7) (R 7) [96,288,9,66,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29531 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29532 : Route 9 := (fun mask => (mask,id))

def c29532 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29532 : Upper (D 7) (R 7) [96,288,9,66,129,16] 13 := by
  apply FastRouting.sound _ _ [96,288,9,66,129,16] 13 (by decide) (choices 1) [2,4,128] r29532 c29532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11338
  · exact u11339
  · exact u11340

def r29533 : Route 9 := (fun mask => (mask,id))

def c29533 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29533 : Upper (D 7) (R 7) [96,288,9,66,129,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,66,129,128] 13 (by decide) (choices 1) [2,4,16] r29533 c29533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11341
  · exact u11342
  · exact u11343

def b29534 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 290 13 74 146 33 212 148 404), lower := (rows 97 290 13 74 146 33 64 128 256), losses := [] }

theorem u29534 : Upper (D 7) (R 7) [96,288,9,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29535 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 290 13 74 146 36 209 145 401), lower := (rows 97 290 13 74 146 36 64 128 256), losses := [] }

theorem u29535 : Upper (D 7) (R 7) [96,288,9,66,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29535 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29536 : Route 9 := (fun mask => (mask,id))

def c29536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29536 : Upper (D 7) (R 7) [96,288,9,66,130,16] 13 := by
  apply FastRouting.sound _ _ [96,288,9,66,130,16] 13 (by decide) (choices 1) [1,4,128] r29536 c29536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11344
  · exact u11345
  · exact u11346

def r29537 : Route 9 := (fun mask => (mask,id))

def c29537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29537 : Upper (D 7) (R 7) [96,288,9,66,130,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,66,130,128] 13 (by decide) (choices 1) [1,4,16] r29537 c29537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11347
  · exact u11348
  · exact u11349

def b29538 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 290 13 74 148 33 210 146 402), lower := (rows 97 290 13 74 148 33 64 128 256), losses := [] }

theorem u29538 : Upper (D 7) (R 7) [96,288,9,66,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29539 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 144, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 13 74 148 34 209 145 401), lower := (rows 97 290 13 74 148 34 64 128 256), losses := [] }

theorem u29539 : Upper (D 7) (R 7) [96,288,9,66,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29540 : Route 9 := (fun mask => (mask,id))

def c29540 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29540 : Upper (D 7) (R 7) [96,288,9,66,132,16] 13 := by
  apply FastRouting.sound _ _ [96,288,9,66,132,16] 13 (by decide) (choices 1) [1,2,128] r29540 c29540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11350
  · exact u11351
  · exact u11352

def r29541 : Route 9 := (fun mask => (mask,id))

def c29541 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29541 : Upper (D 7) (R 7) [96,288,9,66,132,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,66,132,128] 13 (by decide) (choices 1) [1,2,16] r29541 c29541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11353
  · exact u11354
  · exact u11355

def b29542 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 290 13 88 22 33 194 130 386), lower := (rows 97 290 13 88 22 33 64 128 256), losses := [] }

theorem u29542 : Upper (D 7) (R 7) [96,288,9,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29543 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(1,0),(1,6),(1,7)], upper := (rows 97 290 13 88 22 34 193 129 385), lower := (rows 97 290 13 88 22 34 64 128 256), losses := [] }

theorem u29543 : Upper (D 7) (R 7) [96,288,9,80,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29544 : Route 9 := (fun mask => (mask,id))

def c29544 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29544 : Upper (D 7) (R 7) [96,288,9,80,6,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,80,6,128] 13 (by decide) (choices 1) [1,2,128] r29544 c29544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11356
  · exact u11357
  · exact u11358

def b29545 : PairBound 9 := { available := 134, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 97 290 13 88 145 34 198 134 390), lower := (rows 97 290 13 88 145 34 64 128 256), losses := [] }

theorem u29545 : Upper (D 7) (R 7) [96,288,9,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29546 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 290 13 88 145 36 194 130 386), lower := (rows 97 290 13 88 145 36 64 128 256), losses := [] }

theorem u29546 : Upper (D 7) (R 7) [96,288,9,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29546 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29547 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 2, region := 418, targets := 1 }], pairs := [(0,1),(1,0),(1,6),(4,6)], upper := (rows 97 290 13 88 145 160 70 134 262), lower := (rows 97 290 13 88 145 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 97 288 13 125 177 160 64 160 256) }] }

theorem u29547 : Upper (D 7) (R 7) [96,288,9,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29548 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 290 13 88 146 33 198 134 390), lower := (rows 97 290 13 88 146 33 64 128 256), losses := [] }

theorem u29548 : Upper (D 7) (R 7) [96,288,9,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29549 : PairBound 9 := { available := 133, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 97 290 13 88 146 34 197 133 389), lower := (rows 97 290 13 88 146 34 64 128 256), losses := [] }

theorem u29549 : Upper (D 7) (R 7) [96,288,9,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29550 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 290 13 88 146 36 195 131 387), lower := (rows 97 290 13 88 146 36 64 128 256), losses := [] }

theorem u29550 : Upper (D 7) (R 7) [96,288,9,80,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29550 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29551 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(0,1),(1,6),(2,1),(4,6)], upper := (rows 97 290 13 88 146 160 71 135 263), lower := (rows 97 290 13 88 146 160 64 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 97 288 13 125 176 160 64 160 256) }] }

theorem u29551 : Upper (D 7) (R 7) [96,288,9,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29552 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 290 13 88 148 33 194 130 386), lower := (rows 97 290 13 88 148 33 64 128 256), losses := [] }

theorem u29552 : Upper (D 7) (R 7) [96,288,9,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29553 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(4,6)], upper := (rows 97 290 13 88 148 34 195 131 387), lower := (rows 97 290 13 88 148 34 64 128 256), losses := [] }

theorem u29553 : Upper (D 7) (R 7) [96,288,9,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29554 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 5, region := 323, targets := 128 }], pairs := [(0,7),(1,6),(1,7),(4,6)], upper := (rows 97 290 13 88 148 160 67 131 259), lower := (rows 97 290 13 88 148 160 64 128 256), losses := [] }

theorem u29554 : Upper (D 7) (R 7) [96,288,9,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29555 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 200, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,0),(3,5)], upper := (rows 97 290 13 138 22 33 208 208 464), lower := (rows 97 290 13 138 22 33 64 128 256), losses := [] }

theorem u29555 : Upper (D 7) (R 7) [96,288,9,130,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29556 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 193, targets := 2 }], pairs := [(0,1),(2,1),(3,5)], upper := (rows 97 290 13 138 22 48 193 193 449), lower := (rows 97 290 13 138 22 48 64 128 256), losses := [{ target := 1, region := (rows 51 0 12 8 16 48 127 191 319), good := (rows 481 481 461 461 501 497 64 128 256) },{ target := 5, region := (rows 1 2 4 24 16 0 69 133 261), good := (rows 449 258 461 138 478 24 64 128 256) }] }

theorem u29556 : Upper (D 7) (R 7) [96,288,9,130,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29556 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29557 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 13 138 22 96 209 145 401), lower := (rows 97 290 13 138 22 96 64 128 256), losses := [] }

theorem u29557 : Upper (D 7) (R 7) [96,288,9,130,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29558 : Route 9 := (fun mask => (mask,id))

def c29558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29558 : Upper (D 7) (R 7) [96,288,9,130,6,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,6,128] 13 (by decide) (choices 1) [1,16] r29558 c29558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11359
  · exact u11360

def r29559 : Route 9 := (fun mask => (mask,id))

def c29559 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29559 : Upper (D 7) (R 7) [96,288,9,130,66,1] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,66,1] 13 (by decide) (choices 1) [4,16,128] r29559 c29559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11361
  · exact u11362
  · exact u11363

def r29560 : Route 9 := (fun mask => (mask,id))

def c29560 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29560 : Upper (D 7) (R 7) [96,288,9,130,66,4] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,66,4] 13 (by decide) (choices 1) [1,16,128] r29560 c29560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11364
  · exact u11365
  · exact u11366

def b29561 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 13 138 82 48 197 133 389), lower := (rows 97 290 13 138 82 48 64 128 256), losses := [] }

theorem u29561 : Upper (D 7) (R 7) [96,288,9,130,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29561 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29562 : Route 9 := (fun mask => (mask,id))

def c29562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29562 : Upper (D 7) (R 7) [96,288,9,130,66,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,66,128] 13 (by decide) (choices 1) [1,4,16] r29562 c29562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11367
  · exact u11368
  · exact u11369

def b29563 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,6),(3,6)], upper := (rows 97 290 13 138 84 33 210 146 402), lower := (rows 97 290 13 138 84 33 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 37 0 144 272), good := (rows 33 290 45 138 446 33 0 128 256) }] }

theorem u29563 : Upper (D 7) (R 7) [96,288,9,130,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29564 : PairBound 9 := { available := 145, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 13 138 84 34 209 145 401), lower := (rows 97 290 13 138 84 34 64 128 256), losses := [] }

theorem u29564 : Upper (D 7) (R 7) [96,288,9,130,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29565 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 13 138 84 48 195 131 387), lower := (rows 97 290 13 138 84 48 64 128 256), losses := [] }

theorem u29565 : Upper (D 7) (R 7) [96,288,9,130,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29565 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29566 : Route 9 := (fun mask => (mask,id))

def c29566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29566 : Upper (D 7) (R 7) [96,288,9,130,68,128] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,68,128] 13 (by decide) (choices 1) [1,2,16] r29566 c29566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11370
  · exact u11371
  · exact u11372

def b29567 : PairBound 9 := { available := 84, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 13 138 145 34 84 212 340), lower := (rows 97 290 13 138 145 34 64 128 256), losses := [] }

theorem u29567 : Upper (D 7) (R 7) [96,288,9,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29568 : Route 9 := (fun mask => (mask,id))

def c29568 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29568 : Upper (D 7) (R 7) [96,288,9,130,129,4] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,129,4] 13 (by decide) (choices 1) [2,16] r29568 c29568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11373
  · exact u11374

def r29569 : Route 9 := (fun mask => (mask,id))

def c29569 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29569 : Upper (D 7) (R 7) [96,288,9,130,129,16] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,129,16] 13 (by decide) (choices 1) [2,4] r29569 c29569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11375
  · exact u11376

def b29570 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 13 138 145 96 86 150 278), lower := (rows 97 290 13 138 145 96 64 128 256), losses := [] }

theorem u29570 : Upper (D 7) (R 7) [96,288,9,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29570 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29571 : Route 9 := (fun mask => (mask,id))

def c29571 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29571 : Upper (D 7) (R 7) [96,288,9,130,132,1] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,132,1] 13 (by decide) (choices 1) [2,16] r29571 c29571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11377
  · exact u11378

def b29572 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 13 138 148 34 81 209 337), lower := (rows 97 290 13 138 148 34 64 128 256), losses := [] }

theorem u29572 : Upper (D 7) (R 7) [96,288,9,130,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29573 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 290 13 138 148 48 67 195 323), lower := (rows 97 290 13 138 148 48 64 128 256), losses := [{ target := 7, region := (rows 51 51 12 8 16 48 127 0 319), good := (rows 355 355 335 335 375 371 64 0 256) }] }

theorem u29573 : Upper (D 7) (R 7) [96,288,9,130,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29573 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29574 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 290 13 138 148 96 83 147 275), lower := (rows 97 290 13 138 148 96 64 128 256), losses := [] }

theorem u29574 : Upper (D 7) (R 7) [96,288,9,130,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29575 : Route 9 := (fun mask => (mask,id))

def c29575 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29575 : Upper (D 7) (R 7) [96,288,9,130,192,1] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,192,1] 13 (by decide) (choices 1) [2,4,16] r29575 c29575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11379
  · exact u11380
  · exact u11381

def b29576 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 34, targets := 193 },{ cop := 2, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 97 290 13 138 208 34 85 149 277), lower := (rows 97 290 13 138 208 34 64 128 256), losses := [] }

theorem u29576 : Upper (D 7) (R 7) [96,288,9,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29577 : Route 9 := (fun mask => (mask,id))

def c29577 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29577 : Upper (D 7) (R 7) [96,288,9,130,192,4] 13 := by
  apply FastRouting.sound _ _ [96,288,9,130,192,4] 13 (by decide) (choices 1) [1,2,16] r29577 c29577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11382
  · exact u11383
  · exact u11384

def b29578 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 290 13 138 208 48 71 135 263), lower := (rows 97 290 13 138 208 48 64 128 256), losses := [] }

theorem u29578 : Upper (D 7) (R 7) [96,288,9,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29578 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29579 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 290 13 140 82 33 210 146 402), lower := (rows 97 290 13 140 82 33 64 128 256), losses := [] }

theorem u29579 : Upper (D 7) (R 7) [96,288,9,132,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u29579
end Delivery.IrregularNine14.P07
