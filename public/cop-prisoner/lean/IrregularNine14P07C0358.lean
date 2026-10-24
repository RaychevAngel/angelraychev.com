import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0105

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21480 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 35 262 100 26 145 96 201 137 393), lower := (rows 35 262 100 26 145 96 64 128 256), losses := [] }

theorem u21480 : Upper (D 7) (R 7) [34,260,96,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21481 : Route 9 := (fun mask => (mask,id))

def c21481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21481 : Upper (D 7) (R 7) [34,260,96,18,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,96,18,129,128] 13 (by decide) (choices 1) [1,8] r21481 c21481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6300
  · exact u6301

def b21482 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 100 26 152 33 193 193 449), lower := (rows 35 262 100 26 152 33 64 128 256), losses := [] }

theorem u21482 : Upper (D 7) (R 7) [34,260,96,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21483 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 35 262 100 26 152 96 193 129 385), lower := (rows 35 262 100 26 152 96 64 128 256), losses := [] }

theorem u21483 : Upper (D 7) (R 7) [34,260,96,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21484 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 35 262 100 26 152 160 65 193 321), lower := (rows 35 262 100 26 152 160 64 128 256), losses := [] }

theorem u21484 : Upper (D 7) (R 7) [34,260,96,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21485 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 100 26 208 33 201 137 393), lower := (rows 35 262 100 26 208 33 64 128 256), losses := [] }

theorem u21485 : Upper (D 7) (R 7) [34,260,96,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21486 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 35 262 100 26 208 40 193 129 385), lower := (rows 35 262 100 26 208 40 64 128 256), losses := [] }

theorem u21486 : Upper (D 7) (R 7) [34,260,96,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21486 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21487 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 35 262 100 26 208 160 73 137 265), lower := (rows 35 262 100 26 208 160 64 128 256), losses := [] }

theorem u21487 : Upper (D 7) (R 7) [34,260,96,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21488 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 262 100 73 145 34 216 152 408), lower := (rows 35 262 100 73 145 34 64 128 256), losses := [] }

theorem u21488 : Upper (D 7) (R 7) [34,260,96,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21489 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 262 100 73 145 40 210 146 402), lower := (rows 35 262 100 73 145 40 64 128 256), losses := [] }

theorem u21489 : Upper (D 7) (R 7) [34,260,96,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21489 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21490 : Route 9 := (fun mask => (mask,id))

def c21490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21490 : Upper (D 7) (R 7) [34,260,96,65,129,16] 13 := by
  apply FastRouting.sound _ _ [34,260,96,65,129,16] 13 (by decide) (choices 1) [2,8,128] r21490 c21490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6302
  · exact u6303
  · exact u6304

def r21491 : Route 9 := (fun mask => (mask,id))

def c21491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21491 : Upper (D 7) (R 7) [34,260,96,65,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,96,65,129,128] 13 (by decide) (choices 1) [2,8,16] r21491 c21491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6305
  · exact u6306
  · exact u6307

def b21492 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 100 73 146 33 216 152 408), lower := (rows 35 262 100 73 146 33 64 128 256), losses := [] }

theorem u21492 : Upper (D 7) (R 7) [34,260,96,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21493 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 262 100 73 146 40 209 145 401), lower := (rows 35 262 100 73 146 40 64 128 256), losses := [] }

theorem u21493 : Upper (D 7) (R 7) [34,260,96,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21493 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21494 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 35 262 100 73 146 48 201 137 393), lower := (rows 35 262 100 73 146 48 64 128 256), losses := [] }

theorem u21494 : Upper (D 7) (R 7) [34,260,96,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21494 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21495 : Route 9 := (fun mask => (mask,id))

def c21495 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21495 : Upper (D 7) (R 7) [34,260,96,65,130,128] 13 := by
  apply FastRouting.sound _ _ [34,260,96,65,130,128] 13 (by decide) (choices 1) [1,8,16] r21495 c21495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6308
  · exact u6309
  · exact u6310

def b21496 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 100 73 152 33 210 146 402), lower := (rows 35 262 100 73 152 33 64 128 256), losses := [] }

theorem u21496 : Upper (D 7) (R 7) [34,260,96,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21497 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 262 100 73 152 34 209 145 401), lower := (rows 35 262 100 73 152 34 64 128 256), losses := [] }

theorem u21497 : Upper (D 7) (R 7) [34,260,96,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21498 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 262 100 73 152 48 195 131 387), lower := (rows 35 262 100 73 152 48 64 128 256), losses := [] }

theorem u21498 : Upper (D 7) (R 7) [34,260,96,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21498 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21499 : Route 9 := (fun mask => (mask,id))

def c21499 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21499 : Upper (D 7) (R 7) [34,260,96,65,136,128] 13 := by
  apply FastRouting.sound _ _ [34,260,96,65,136,128] 13 (by decide) (choices 1) [1,2,16] r21499 c21499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6311
  · exact u6312
  · exact u6313

def b21500 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 100 88 145 33 202 138 394), lower := (rows 35 262 100 88 145 33 64 128 256), losses := [] }

theorem u21500 : Upper (D 7) (R 7) [34,260,96,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21501 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 262 100 88 145 34 201 137 393), lower := (rows 35 262 100 88 145 34 64 128 256), losses := [] }

theorem u21501 : Upper (D 7) (R 7) [34,260,96,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21502 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 262 100 88 145 40 195 131 387), lower := (rows 35 262 100 88 145 40 64 128 256), losses := [] }

theorem u21502 : Upper (D 7) (R 7) [34,260,96,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21502 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21503 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 35 262 100 88 145 160 75 139 267), lower := (rows 35 262 100 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 262 100 124 176 160 64 160 256) },{ target := 1, region := (rows 1 0 12 8 16 176 64 128 256), good := (rows 33 260 100 124 177 160 64 160 256) }] }

theorem u21503 : Upper (D 7) (R 7) [34,260,96,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21504 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 100 88 146 33 201 137 393), lower := (rows 35 262 100 88 146 33 64 128 256), losses := [] }

theorem u21504 : Upper (D 7) (R 7) [34,260,96,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21505 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 262 100 88 146 40 193 129 385), lower := (rows 35 262 100 88 146 40 64 128 256), losses := [] }

theorem u21505 : Upper (D 7) (R 7) [34,260,96,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21505 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21506 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(3,5),(4,5)], upper := (rows 35 262 100 88 146 160 73 137 265), lower := (rows 35 262 100 88 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 34 262 100 124 178 160 64 160 256) }] }

theorem u21506 : Upper (D 7) (R 7) [34,260,96,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21507 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 100 137 146 33 88 216 344), lower := (rows 35 262 100 137 146 33 64 128 256), losses := [] }

theorem u21507 : Upper (D 7) (R 7) [34,260,96,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21508 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 262 100 137 146 40 81 209 337), lower := (rows 35 262 100 137 146 40 64 128 256), losses := [] }

theorem u21508 : Upper (D 7) (R 7) [34,260,96,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21508 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21509 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 35 262 100 137 146 48 73 201 329), lower := (rows 35 262 100 137 146 48 64 128 256), losses := [] }

theorem u21509 : Upper (D 7) (R 7) [34,260,96,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21509 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21510 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 35 262 100 137 146 96 89 153 281), lower := (rows 35 262 100 137 146 96 64 128 256), losses := [] }

theorem u21510 : Upper (D 7) (R 7) [34,260,96,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21511 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 100 137 208 33 90 154 282), lower := (rows 35 262 100 137 208 33 64 128 256), losses := [] }

theorem u21511 : Upper (D 7) (R 7) [34,260,96,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21512 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 262 100 137 208 34 89 153 281), lower := (rows 35 262 100 137 208 34 64 128 256), losses := [] }

theorem u21512 : Upper (D 7) (R 7) [34,260,96,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21513 : Route 9 := (fun mask => (mask,id))

def c21513 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21513 : Upper (D 7) (R 7) [34,260,96,129,192,8] 13 := by
  apply FastRouting.sound _ _ [34,260,96,129,192,8] 13 (by decide) (choices 1) [1,2,16] r21513 c21513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6314
  · exact u6315
  · exact u6316

def b21514 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 262 100 137 208 48 75 139 267), lower := (rows 35 262 100 137 208 48 64 128 256), losses := [] }

theorem u21514 : Upper (D 7) (R 7) [34,260,96,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21514 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21515 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 100 138 208 33 89 153 281), lower := (rows 35 262 100 138 208 33 64 128 256), losses := [] }

theorem u21515 : Upper (D 7) (R 7) [34,260,96,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21516 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 35 262 100 138 208 40 81 145 273), lower := (rows 35 262 100 138 208 40 64 128 256), losses := [] }

theorem u21516 : Upper (D 7) (R 7) [34,260,96,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21516 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21517 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 262 100 138 208 48 73 137 265), lower := (rows 35 262 100 138 208 48 64 128 256), losses := [] }

theorem u21517 : Upper (D 7) (R 7) [34,260,96,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21517 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21518 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 3, region := 228, targets := 2 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(0,7),(2,1),(3,6)], upper := (rows 35 262 196 25 82 33 232 168 424), lower := (rows 35 262 196 25 82 33 64 128 256), losses := [] }

theorem u21518 : Upper (D 7) (R 7) [34,260,192,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21519 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 4, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 262 196 25 82 40 225 161 417), lower := (rows 35 262 196 25 82 40 64 128 256), losses := [] }

theorem u21519 : Upper (D 7) (R 7) [34,260,192,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21519 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21520 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(3,6),(3,7),(4,7)], upper := (rows 35 262 196 25 82 160 105 169 297), lower := (rows 35 262 196 25 82 160 64 128 256), losses := [] }

theorem u21520 : Upper (D 7) (R 7) [34,260,192,17,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21521 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(1,0),(1,6),(2,0)], upper := (rows 35 262 196 25 88 33 226 162 418), lower := (rows 35 262 196 25 88 33 64 128 256), losses := [] }

theorem u21521 : Upper (D 7) (R 7) [34,260,192,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21522 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 196 25 88 34 225 161 417), lower := (rows 35 262 196 25 88 34 64 128 256), losses := [] }

theorem u21522 : Upper (D 7) (R 7) [34,260,192,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21523 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 35 262 196 25 88 160 99 163 291), lower := (rows 35 262 196 25 88 160 64 128 256), losses := [] }

theorem u21523 : Upper (D 7) (R 7) [34,260,192,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21524 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 196 25 112 33 202 138 394), lower := (rows 35 262 196 25 112 33 64 128 256), losses := [] }

theorem u21524 : Upper (D 7) (R 7) [34,260,192,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21525 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 196 25 112 34 201 137 393), lower := (rows 35 262 196 25 112 34 64 128 256), losses := [] }

theorem u21525 : Upper (D 7) (R 7) [34,260,192,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21526 : Route 9 := (fun mask => (mask,id))

def c21526 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21526 : Upper (D 7) (R 7) [34,260,192,17,96,8] 13 := by
  apply FastRouting.sound _ _ [34,260,192,17,96,8] 13 (by decide) (choices 1) [1,2,128] r21526 c21526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6317
  · exact u6318
  · exact u6319

def b21527 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 2, region := 48, targets := 3 }], pairs := [(3,7),(4,0),(4,1),(4,7)], upper := (rows 35 262 196 25 112 160 75 139 267), lower := (rows 35 262 196 25 112 160 64 128 256), losses := [] }

theorem u21527 : Upper (D 7) (R 7) [34,260,192,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21528 : Route 9 := (fun mask => (mask,id))

def c21528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u21528 : Upper (D 7) (R 7) [34,260,192,18,65,1] 13 := by
  apply FastRouting.sound _ _ [34,260,192,18,65,1] 13 (by decide) (choices 1) [8,32,128] r21528 c21528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6320
  · exact u6321
  · exact u6322

def b21529 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 262 196 26 81 40 225 161 417), lower := (rows 35 262 196 26 81 40 64 128 256), losses := [] }

theorem u21529 : Upper (D 7) (R 7) [34,260,192,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21529 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21530 : Route 9 := (fun mask => (mask,id))

def c21530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21530 : Upper (D 7) (R 7) [34,260,192,18,65,128] 13 := by
  apply FastRouting.sound _ _ [34,260,192,18,65,128] 13 (by decide) (choices 1) [1,8,32] r21530 c21530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6323
  · exact u6324
  · exact u6325

def b21531 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 0, region := 196, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(2,1)], upper := (rows 35 262 196 26 88 33 225 161 417), lower := (rows 35 262 196 26 88 33 64 128 256), losses := [] }

theorem u21531 : Upper (D 7) (R 7) [34,260,192,18,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21532 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 35 262 196 26 88 160 97 161 289), lower := (rows 35 262 196 26 88 160 64 128 256), losses := [] }

theorem u21532 : Upper (D 7) (R 7) [34,260,192,18,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21533 : Route 9 := (fun mask => (mask,id))

def c21533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21533 : Upper (D 7) (R 7) [34,260,192,18,96,1] 13 := by
  apply FastRouting.sound _ _ [34,260,192,18,96,1] 13 (by decide) (choices 1) [1,8,128] r21533 c21533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6326
  · exact u6327
  · exact u6328

def b21534 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 35 262 196 26 112 40 193 129 385), lower := (rows 35 262 196 26 112 40 64 128 256), losses := [] }

theorem u21534 : Upper (D 7) (R 7) [34,260,192,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21534 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21535 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 2, region := 48, targets := 3 }], pairs := [(3,7),(4,0),(4,1),(4,7)], upper := (rows 35 262 196 26 112 160 73 137 265), lower := (rows 35 262 196 26 112 160 64 128 256), losses := [] }

theorem u21535 : Upper (D 7) (R 7) [34,260,192,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21536 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 196 56 81 33 202 138 394), lower := (rows 35 262 196 56 81 33 64 128 256), losses := [] }

theorem u21536 : Upper (D 7) (R 7) [34,260,192,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21537 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 196 56 81 34 201 137 393), lower := (rows 35 262 196 56 81 34 64 128 256), losses := [] }

theorem u21537 : Upper (D 7) (R 7) [34,260,192,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21538 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 262 196 56 81 40 195 131 387), lower := (rows 35 262 196 56 81 40 64 128 256), losses := [] }

theorem u21538 : Upper (D 7) (R 7) [34,260,192,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21538 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21539 : Route 9 := (fun mask => (mask,id))

def c21539 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21539 : Upper (D 7) (R 7) [34,260,192,48,65,128] 13 := by
  apply FastRouting.sound _ _ [34,260,192,48,65,128] 13 (by decide) (choices 1) [1,2,8] r21539 c21539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6329
  · exact u6330
  · exact u6331

#print axioms u21539
end Delivery.IrregularNine14.P07
