import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0135
import IrregularNine14P07C0136

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24480 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 3, region := 242, targets := 1 }], pairs := [(1,0),(2,1),(2,5),(4,0)], upper := (rows 37 98 261 25 26 34 192 192 448), lower := (rows 37 98 261 25 26 34 64 128 256), losses := [] }

theorem u24480 : Upper (D 7) (R 7) [36,96,257,17,10,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24481 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 261 25 26 96 194 130 386), lower := (rows 37 98 261 25 26 96 64 128 256), losses := [] }

theorem u24481 : Upper (D 7) (R 7) [36,96,257,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24482 : Route 9 := (fun mask => (mask,id))

def c24482 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24482 : Upper (D 7) (R 7) [36,96,257,17,10,128] 13 := by
  apply FastRouting.sound _ _ [36,96,257,17,10,128] 13 (by decide) (choices 1) [2,128] r24482 c24482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8109
  · exact u8110

def b24483 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 3, region := 452, targets := 34 }], pairs := [(1,0),(2,1),(2,5),(4,0)], upper := (rows 37 98 261 25 146 34 200 200 456), lower := (rows 37 98 261 25 146 34 64 128 256), losses := [] }

theorem u24483 : Upper (D 7) (R 7) [36,96,257,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24484 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 210, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 98 261 25 146 40 194 194 450), lower := (rows 37 98 261 25 146 40 64 128 256), losses := [] }

theorem u24484 : Upper (D 7) (R 7) [36,96,257,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24484 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24485 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 261 25 146 96 202 138 394), lower := (rows 37 98 261 25 146 96 64 128 256), losses := [] }

theorem u24485 : Upper (D 7) (R 7) [36,96,257,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24486 : Route 9 := (fun mask => (mask,id))

def c24486 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24486 : Upper (D 7) (R 7) [36,96,257,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,257,17,130,128] 13 (by decide) (choices 1) [2,8] r24486 c24486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8111
  · exact u8112

def b24487 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(4,0)], upper := (rows 37 98 261 25 152 34 194 194 450), lower := (rows 37 98 261 25 152 34 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 13 17 0 98 162 290), good := (rows 477 450 285 29 152 450 64 128 256) }] }

theorem u24487 : Upper (D 7) (R 7) [36,96,257,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24488 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 261 25 152 96 194 130 386), lower := (rows 37 98 261 25 152 96 64 128 256), losses := [] }

theorem u24488 : Upper (D 7) (R 7) [36,96,257,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24489 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 261 25 152 160 66 194 322), lower := (rows 37 98 261 25 152 160 64 128 256), losses := [] }

theorem u24489 : Upper (D 7) (R 7) [36,96,257,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24490 : Route 9 := (fun mask => (mask,id))

def c24490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24490 : Upper (D 7) (R 7) [36,96,257,17,192,2] 13 := by
  apply FastRouting.sound _ _ [36,96,257,17,192,2] 13 (by decide) (choices 1) [2,8,128] r24490 c24490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8113
  · exact u8114
  · exact u8115

def b24491 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 210, targets := 1 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(1,0),(4,0)], upper := (rows 37 98 261 25 208 40 194 130 386), lower := (rows 37 98 261 25 208 40 64 128 256), losses := [] }

theorem u24491 : Upper (D 7) (R 7) [36,96,257,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24491 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24492 : Route 9 := (fun mask => (mask,id))

def c24492 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24492 : Upper (D 7) (R 7) [36,96,257,17,192,128] 13 := by
  apply FastRouting.sound _ _ [36,96,257,17,192,128] 13 (by decide) (choices 1) [2,8] r24492 c24492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8116
  · exact u8117

def r24493 : Route 9 := (fun mask => (mask,id))

def c24493 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24493 : Upper (D 7) (R 7) [36,96,257,18,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,257,18,129,2] 13 (by decide) (choices 1) [8,128] r24493 c24493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8118
  · exact u8119

def r24494 : Route 9 := (fun mask => (mask,id))

def c24494 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24494 : Upper (D 7) (R 7) [36,96,257,18,129,8] 13 := by
  apply FastRouting.sound _ _ [36,96,257,18,129,8] 13 (by decide) (choices 1) [2,128] r24494 c24494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8120
  · exact u8121

def b24495 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 261 26 145 96 202 138 394), lower := (rows 37 98 261 26 145 96 64 128 256), losses := [] }

theorem u24495 : Upper (D 7) (R 7) [36,96,257,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24496 : Route 9 := (fun mask => (mask,id))

def c24496 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24496 : Upper (D 7) (R 7) [36,96,257,18,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,257,18,129,128] 13 (by decide) (choices 1) [2,8] r24496 c24496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8122
  · exact u8123

def b24497 : PairBound 9 := { available := 194, camps := [{ cop := 8, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 261 26 152 33 194 194 450), lower := (rows 37 98 261 26 152 33 64 128 256), losses := [] }

theorem u24497 : Upper (D 7) (R 7) [36,96,257,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24498 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 37 98 261 26 152 34 193 193 449), lower := (rows 37 98 261 26 152 34 64 128 256), losses := [] }

theorem u24498 : Upper (D 7) (R 7) [36,96,257,18,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24499 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 261 26 152 96 195 131 387), lower := (rows 37 98 261 26 152 96 64 128 256), losses := [] }

theorem u24499 : Upper (D 7) (R 7) [36,96,257,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24500 : Route 9 := (fun mask => (mask,id))

def c24500 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24500 : Upper (D 7) (R 7) [36,96,257,18,136,128] 13 := by
  apply FastRouting.sound _ _ [36,96,257,18,136,128] 13 (by decide) (choices 1) [1,2] r24500 c24500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8124
  · exact u8125

def b24501 : PairBound 9 := { available := 138, camps := [{ cop := 8, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 261 26 208 33 202 138 394), lower := (rows 37 98 261 26 208 33 64 128 256), losses := [] }

theorem u24501 : Upper (D 7) (R 7) [36,96,257,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24502 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 98 261 26 208 34 201 137 393), lower := (rows 37 98 261 26 208 34 64 128 256), losses := [] }

theorem u24502 : Upper (D 7) (R 7) [36,96,257,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24503 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 261 26 208 40 195 131 387), lower := (rows 37 98 261 26 208 40 64 128 256), losses := [] }

theorem u24503 : Upper (D 7) (R 7) [36,96,257,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24503 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24504 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 42, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 98 261 26 208 160 75 139 267), lower := (rows 37 98 261 26 208 160 64 128 256), losses := [] }

theorem u24504 : Upper (D 7) (R 7) [36,96,257,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24505 : Route 9 := (fun mask => (mask,id))

def c24505 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24505 : Upper (D 7) (R 7) [36,96,257,65,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,257,65,130,2] 13 (by decide) (choices 1) [8,16,128] r24505 c24505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8126
  · exact u8127
  · exact u8128

def b24506 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 261 73 146 40 210 146 402), lower := (rows 37 98 261 73 146 40 64 128 256), losses := [] }

theorem u24506 : Upper (D 7) (R 7) [36,96,257,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24506 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24507 : Route 9 := (fun mask => (mask,id))

def c24507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24507 : Upper (D 7) (R 7) [36,96,257,65,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,257,65,130,16] 13 (by decide) (choices 1) [2,8,128] r24507 c24507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8129
  · exact u8130
  · exact u8131

def r24508 : Route 9 := (fun mask => (mask,id))

def c24508 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24508 : Upper (D 7) (R 7) [36,96,257,65,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,257,65,130,128] 13 (by decide) (choices 1) [2,8,16] r24508 c24508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8132
  · exact u8133
  · exact u8134

def r24509 : Route 9 := (fun mask => (mask,id))

def c24509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24509 : Upper (D 7) (R 7) [36,96,257,65,136,2] 13 := by
  apply FastRouting.sound _ _ [36,96,257,65,136,2] 13 (by decide) (choices 1) [2,16,128] r24509 c24509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8135
  · exact u8136
  · exact u8137

def b24510 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 3, region := 178, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 261 73 152 48 194 130 386), lower := (rows 37 98 261 73 152 48 64 128 256), losses := [] }

theorem u24510 : Upper (D 7) (R 7) [36,96,257,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24510 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24511 : Route 9 := (fun mask => (mask,id))

def c24511 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24511 : Upper (D 7) (R 7) [36,96,257,65,136,128] 13 := by
  apply FastRouting.sound _ _ [36,96,257,65,136,128] 13 (by decide) (choices 1) [2,16] r24511 c24511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8138
  · exact u8139

def r24512 : Route 9 := (fun mask => (mask,id))

def c24512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24512 : Upper (D 7) (R 7) [36,96,257,80,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,257,80,129,2] 13 (by decide) (choices 1) [2,8,128] r24512 c24512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8140
  · exact u8141
  · exact u8142

def b24513 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 261 88 145 40 194 130 386), lower := (rows 37 98 261 88 145 40 64 128 256), losses := [] }

theorem u24513 : Upper (D 7) (R 7) [36,96,257,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24513 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24514 : Route 9 := (fun mask => (mask,id))

def c24514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24514 : Upper (D 7) (R 7) [36,96,257,80,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,257,80,129,128] 13 (by decide) (choices 1) [2,8] r24514 c24514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8143
  · exact u8144

def b24515 : PairBound 9 := { available := 138, camps := [{ cop := 8, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 261 88 146 33 202 138 394), lower := (rows 37 98 261 88 146 33 64 128 256), losses := [] }

theorem u24515 : Upper (D 7) (R 7) [36,96,257,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24516 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 261 88 146 34 201 137 393), lower := (rows 37 98 261 88 146 34 64 128 256), losses := [{ target := 6, region := (rows 9 2 12 8 16 50 0 136 264), good := (rows 37 34 261 445 178 34 0 128 256) }] }

theorem u24516 : Upper (D 7) (R 7) [36,96,257,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24517 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 261 88 146 40 195 131 387), lower := (rows 37 98 261 88 146 40 64 128 256), losses := [] }

theorem u24517 : Upper (D 7) (R 7) [36,96,257,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24517 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24518 : Route 9 := (fun mask => (mask,id))

def c24518 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24518 : Upper (D 7) (R 7) [36,96,257,80,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,257,80,130,128] 13 (by decide) (choices 1) [1,2,8] r24518 c24518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8145
  · exact u8146
  · exact u8147

def b24519 : PairBound 9 := { available := 130, camps := [{ cop := 8, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 261 88 152 33 194 130 386), lower := (rows 37 98 261 88 152 33 64 128 256), losses := [] }

theorem u24519 : Upper (D 7) (R 7) [36,96,257,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24520 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 3, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 261 88 152 34 195 131 387), lower := (rows 37 98 261 88 152 34 64 128 256), losses := [] }

theorem u24520 : Upper (D 7) (R 7) [36,96,257,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24521 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 1, region := 261, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 261 88 152 160 67 131 259), lower := (rows 37 98 261 88 152 160 64 128 256), losses := [] }

theorem u24521 : Upper (D 7) (R 7) [36,96,257,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24522 : Route 9 := (fun mask => (mask,id))

def c24522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24522 : Upper (D 7) (R 7) [36,96,257,129,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,257,129,130,2] 13 (by decide) (choices 1) [8,16] r24522 c24522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8148
  · exact u8149

def b24523 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 210, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 98 261 137 146 40 82 210 338), lower := (rows 37 98 261 137 146 40 64 128 256), losses := [] }

theorem u24523 : Upper (D 7) (R 7) [36,96,257,129,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24523 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24524 : Route 9 := (fun mask => (mask,id))

def c24524 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24524 : Upper (D 7) (R 7) [36,96,257,129,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,257,129,130,16] 13 (by decide) (choices 1) [2,8] r24524 c24524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8150
  · exact u8151

def b24525 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 261 137 146 96 90 154 282), lower := (rows 37 98 261 137 146 96 64 128 256), losses := [] }

theorem u24525 : Upper (D 7) (R 7) [36,96,257,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24526 : Route 9 := (fun mask => (mask,id))

def c24526 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24526 : Upper (D 7) (R 7) [36,96,257,129,192,2] 13 := by
  apply FastRouting.sound _ _ [36,96,257,129,192,2] 13 (by decide) (choices 1) [2,8,16] r24526 c24526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8152
  · exact u8153
  · exact u8154

def b24527 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 210, targets := 1 },{ cop := 1, region := 144, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 98 261 137 208 40 82 146 274), lower := (rows 37 98 261 137 208 40 64 128 256), losses := [] }

theorem u24527 : Upper (D 7) (R 7) [36,96,257,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24527 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24528 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 261 137 208 48 74 138 266), lower := (rows 37 98 261 137 208 48 64 128 256), losses := [] }

theorem u24528 : Upper (D 7) (R 7) [36,96,257,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24528 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24529 : PairBound 9 := { available := 26, camps := [{ cop := 8, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 98 261 138 208 33 90 154 282), lower := (rows 37 98 261 138 208 33 64 128 256), losses := [] }

theorem u24529 : Upper (D 7) (R 7) [36,96,257,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24530 : Route 9 := (fun mask => (mask,id))

def c24530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24530 : Upper (D 7) (R 7) [36,96,257,130,192,2] 13 := by
  apply FastRouting.sound _ _ [36,96,257,130,192,2] 13 (by decide) (choices 1) [1,8,16] r24530 c24530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8155
  · exact u8156
  · exact u8157

def r24531 : Route 9 := (fun mask => (mask,id))

def c24531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24531 : Upper (D 7) (R 7) [36,96,257,130,192,8] 13 := by
  apply FastRouting.sound _ _ [36,96,257,130,192,8] 13 (by decide) (choices 1) [1,2,16] r24531 c24531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8158
  · exact u8159
  · exact u8160

def b24532 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 261 138 208 48 75 139 267), lower := (rows 37 98 261 138 208 48 64 128 256), losses := [] }

theorem u24532 : Upper (D 7) (R 7) [36,96,257,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24532 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24533 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 98 262 11 81 40 208 144 400), lower := (rows 37 98 262 11 81 40 64 128 256), losses := [] }

theorem u24533 : Upper (D 7) (R 7) [36,96,258,3,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24533 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24534 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 262 11 81 48 200 136 392), lower := (rows 37 98 262 11 81 48 64 128 256), losses := [] }

theorem u24534 : Upper (D 7) (R 7) [36,96,258,3,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24534 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24535 : Route 9 := (fun mask => (mask,id))

def c24535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24535 : Upper (D 7) (R 7) [36,96,258,3,65,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,3,65,128] 13 (by decide) (choices 1) [8,16,128] r24535 c24535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8161
  · exact u8162
  · exact u8163

def b24536 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 98 262 11 88 33 208 144 400), lower := (rows 37 98 262 11 88 33 64 128 256), losses := [] }

theorem u24536 : Upper (D 7) (R 7) [36,96,258,3,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24537 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 262 11 88 48 193 129 385), lower := (rows 37 98 262 11 88 48 64 128 256), losses := [] }

theorem u24537 : Upper (D 7) (R 7) [36,96,258,3,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24537 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24538 : Route 9 := (fun mask => (mask,id))

def c24538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24538 : Upper (D 7) (R 7) [36,96,258,3,72,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,3,72,128] 13 (by decide) (choices 1) [1,16,128] r24538 c24538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8164
  · exact u8165
  · exact u8166

def b24539 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 98 262 11 145 40 208 208 464), lower := (rows 37 98 262 11 145 40 64 128 256), losses := [] }

theorem u24539 : Upper (D 7) (R 7) [36,96,258,3,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24539 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u24539
end Delivery.IrregularNine14.P07
