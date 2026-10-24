import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0136
import IrregularNine14P07C0137

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24540 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 452, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 37 98 262 11 145 48 200 200 456), lower := (rows 37 98 262 11 145 48 64 128 256), losses := [] }

theorem u24540 : Upper (D 7) (R 7) [36,96,258,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24540 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24541 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 262 11 145 96 216 152 408), lower := (rows 37 98 262 11 145 96 64 128 256), losses := [] }

theorem u24541 : Upper (D 7) (R 7) [36,96,258,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24542 : Route 9 := (fun mask => (mask,id))

def c24542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24542 : Upper (D 7) (R 7) [36,96,258,3,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,3,129,128] 13 (by decide) (choices 1) [8,16] r24542 c24542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8167
  · exact u8168

def b24543 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 98 262 11 152 33 208 208 464), lower := (rows 37 98 262 11 152 33 64 128 256), losses := [] }

theorem u24543 : Upper (D 7) (R 7) [36,96,258,3,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24544 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 208, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 37 98 262 11 152 48 193 193 449), lower := (rows 37 98 262 11 152 48 64 128 256), losses := [] }

theorem u24544 : Upper (D 7) (R 7) [36,96,258,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24544 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24545 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 262 11 152 96 209 145 401), lower := (rows 37 98 262 11 152 96 64 128 256), losses := [] }

theorem u24545 : Upper (D 7) (R 7) [36,96,258,3,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24546 : Route 9 := (fun mask => (mask,id))

def c24546 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24546 : Upper (D 7) (R 7) [36,96,258,3,136,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,3,136,128] 13 (by decide) (choices 1) [1,16] r24546 c24546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8169
  · exact u8170

def b24547 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 98 262 11 208 33 216 152 408), lower := (rows 37 98 262 11 208 33 64 128 256), losses := [] }

theorem u24547 : Upper (D 7) (R 7) [36,96,258,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24548 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 98 262 11 208 40 209 145 401), lower := (rows 37 98 262 11 208 40 64 128 256), losses := [] }

theorem u24548 : Upper (D 7) (R 7) [36,96,258,3,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24548 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24549 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 262 11 208 48 201 137 393), lower := (rows 37 98 262 11 208 48 64 128 256), losses := [] }

theorem u24549 : Upper (D 7) (R 7) [36,96,258,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24549 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24550 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 208, targets := 2 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(2,5),(4,1),(4,5)], upper := (rows 37 98 262 11 208 160 89 153 281), lower := (rows 37 98 262 11 208 160 64 128 256), losses := [] }

theorem u24550 : Upper (D 7) (R 7) [36,96,258,3,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24551 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 98 262 25 26 33 192 192 448), lower := (rows 37 98 262 25 26 33 64 128 256), losses := [] }

theorem u24551 : Upper (D 7) (R 7) [36,96,258,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24552 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 262 25 26 96 193 129 385), lower := (rows 37 98 262 25 26 96 64 128 256), losses := [] }

theorem u24552 : Upper (D 7) (R 7) [36,96,258,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24553 : Route 9 := (fun mask => (mask,id))

def c24553 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24553 : Upper (D 7) (R 7) [36,96,258,17,10,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,10,128] 13 (by decide) (choices 1) [1,128] r24553 c24553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8171
  · exact u8172

def b24554 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(2,6)], upper := (rows 37 98 262 25 88 33 194 130 386), lower := (rows 37 98 262 25 88 33 64 128 256), losses := [] }

theorem u24554 : Upper (D 7) (R 7) [36,96,258,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24555 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 262 25 88 34 193 129 385), lower := (rows 37 98 262 25 88 34 64 128 256), losses := [] }

theorem u24555 : Upper (D 7) (R 7) [36,96,258,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24556 : Route 9 := (fun mask => (mask,id))

def c24556 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24556 : Upper (D 7) (R 7) [36,96,258,17,72,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,72,128] 13 (by decide) (choices 1) [1,2,128] r24556 c24556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8173
  · exact u8174
  · exact u8175

def r24557 : Route 9 := (fun mask => (mask,id))

def c24557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24557 : Upper (D 7) (R 7) [36,96,258,17,130,1] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,130,1] 13 (by decide) (choices 1) [8,128] r24557 c24557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8176
  · exact u8177

def r24558 : Route 9 := (fun mask => (mask,id))

def c24558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24558 : Upper (D 7) (R 7) [36,96,258,17,130,8] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,130,8] 13 (by decide) (choices 1) [1,128] r24558 c24558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8178
  · exact u8179

def b24559 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 262 25 146 96 201 137 393), lower := (rows 37 98 262 25 146 96 64 128 256), losses := [] }

theorem u24559 : Upper (D 7) (R 7) [36,96,258,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24560 : Route 9 := (fun mask => (mask,id))

def c24560 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24560 : Upper (D 7) (R 7) [36,96,258,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,130,128] 13 (by decide) (choices 1) [1,8] r24560 c24560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8180
  · exact u8181

def b24561 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 262 25 152 33 194 194 450), lower := (rows 37 98 262 25 152 33 64 128 256), losses := [] }

theorem u24561 : Upper (D 7) (R 7) [36,96,258,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24562 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 262 25 152 34 193 193 449), lower := (rows 37 98 262 25 152 34 64 128 256), losses := [] }

theorem u24562 : Upper (D 7) (R 7) [36,96,258,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24563 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 262 25 152 96 195 131 387), lower := (rows 37 98 262 25 152 96 64 128 256), losses := [] }

theorem u24563 : Upper (D 7) (R 7) [36,96,258,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24564 : Route 9 := (fun mask => (mask,id))

def c24564 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24564 : Upper (D 7) (R 7) [36,96,258,17,136,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,136,128] 13 (by decide) (choices 1) [1,2] r24564 c24564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8182
  · exact u8183

def r24565 : Route 9 := (fun mask => (mask,id))

def c24565 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24565 : Upper (D 7) (R 7) [36,96,258,17,192,1] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,192,1] 13 (by decide) (choices 1) [2,8,128] r24565 c24565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8184
  · exact u8185
  · exact u8186

def b24566 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 262 25 208 34 201 137 393), lower := (rows 37 98 262 25 208 34 64 128 256), losses := [] }

theorem u24566 : Upper (D 7) (R 7) [36,96,258,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24567 : Route 9 := (fun mask => (mask,id))

def c24567 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24567 : Upper (D 7) (R 7) [36,96,258,17,192,8] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,192,8] 13 (by decide) (choices 1) [1,2,128] r24567 c24567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8187
  · exact u8188
  · exact u8189

def r24568 : Route 9 := (fun mask => (mask,id))

def c24568 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24568 : Upper (D 7) (R 7) [36,96,258,17,192,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,17,192,128] 13 (by decide) (choices 1) [1,2,8] r24568 c24568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8190
  · exact u8191
  · exact u8192

def b24569 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 388, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 98 262 26 81 33 200 136 392), lower := (rows 37 98 262 26 81 33 64 128 256), losses := [] }

theorem u24569 : Upper (D 7) (R 7) [36,96,258,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24570 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 262 26 81 40 193 129 385), lower := (rows 37 98 262 26 81 40 64 128 256), losses := [] }

theorem u24570 : Upper (D 7) (R 7) [36,96,258,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24570 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24571 : Route 9 := (fun mask => (mask,id))

def c24571 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24571 : Upper (D 7) (R 7) [36,96,258,18,65,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,18,65,128] 13 (by decide) (choices 1) [1,8,128] r24571 c24571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8193
  · exact u8194
  · exact u8195

def b24572 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 452, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 98 262 26 145 33 200 200 456), lower := (rows 37 98 262 26 145 33 64 128 256), losses := [] }

theorem u24572 : Upper (D 7) (R 7) [36,96,258,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24572 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24573 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 37 98 262 26 145 40 193 193 449), lower := (rows 37 98 262 26 145 40 64 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 17 0 81 145 273), good := (rows 469 66 262 478 465 12 64 128 256) }] }

theorem u24573 : Upper (D 7) (R 7) [36,96,258,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24573 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24574 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 262 26 145 96 201 137 393), lower := (rows 37 98 262 26 145 96 64 128 256), losses := [] }

theorem u24574 : Upper (D 7) (R 7) [36,96,258,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24575 : Route 9 := (fun mask => (mask,id))

def c24575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24575 : Upper (D 7) (R 7) [36,96,258,18,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,18,129,128] 13 (by decide) (choices 1) [1,8] r24575 c24575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8196
  · exact u8197

def b24576 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 98 262 26 152 33 193 193 449), lower := (rows 37 98 262 26 152 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 6 14 19 0 97 161 289), good := (rows 477 478 286 30 152 465 64 128 256) }] }

theorem u24576 : Upper (D 7) (R 7) [36,96,258,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24577 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 262 26 152 96 193 129 385), lower := (rows 37 98 262 26 152 96 64 128 256), losses := [] }

theorem u24577 : Upper (D 7) (R 7) [36,96,258,18,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24577 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24578 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,7)], upper := (rows 37 98 262 26 152 160 65 193 321), lower := (rows 37 98 262 26 152 160 64 128 256), losses := [] }

theorem u24578 : Upper (D 7) (R 7) [36,96,258,18,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24578 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24579 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 98 262 26 208 33 201 137 393), lower := (rows 37 98 262 26 208 33 64 128 256), losses := [] }

theorem u24579 : Upper (D 7) (R 7) [36,96,258,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24579 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24580 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 262 26 208 40 193 129 385), lower := (rows 37 98 262 26 208 40 64 128 256), losses := [] }

theorem u24580 : Upper (D 7) (R 7) [36,96,258,18,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24580 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24581 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 42, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 98 262 26 208 160 73 137 265), lower := (rows 37 98 262 26 208 160 64 128 256), losses := [] }

theorem u24581 : Upper (D 7) (R 7) [36,96,258,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24581 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24582 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 262 73 145 34 216 152 408), lower := (rows 37 98 262 73 145 34 64 128 256), losses := [] }

theorem u24582 : Upper (D 7) (R 7) [36,96,258,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24583 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 262 73 145 40 210 146 402), lower := (rows 37 98 262 73 145 40 64 128 256), losses := [] }

theorem u24583 : Upper (D 7) (R 7) [36,96,258,65,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24583 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24584 : Route 9 := (fun mask => (mask,id))

def c24584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24584 : Upper (D 7) (R 7) [36,96,258,65,129,16] 13 := by
  apply FastRouting.sound _ _ [36,96,258,65,129,16] 13 (by decide) (choices 1) [2,8,128] r24584 c24584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8198
  · exact u8199
  · exact u8200

def r24585 : Route 9 := (fun mask => (mask,id))

def c24585 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24585 : Upper (D 7) (R 7) [36,96,258,65,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,65,129,128] 13 (by decide) (choices 1) [2,8,16] r24585 c24585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8201
  · exact u8202
  · exact u8203

def b24586 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 34, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 262 73 146 33 216 152 408), lower := (rows 37 98 262 73 146 33 64 128 256), losses := [] }

theorem u24586 : Upper (D 7) (R 7) [36,96,258,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24587 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 262 73 146 40 209 145 401), lower := (rows 37 98 262 73 146 40 64 128 256), losses := [] }

theorem u24587 : Upper (D 7) (R 7) [36,96,258,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24587 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24588 : Route 9 := (fun mask => (mask,id))

def c24588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24588 : Upper (D 7) (R 7) [36,96,258,65,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,258,65,130,16] 13 (by decide) (choices 1) [1,8,128] r24588 c24588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8204
  · exact u8205
  · exact u8206

def r24589 : Route 9 := (fun mask => (mask,id))

def c24589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24589 : Upper (D 7) (R 7) [36,96,258,65,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,65,130,128] 13 (by decide) (choices 1) [1,8,16] r24589 c24589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8207
  · exact u8208
  · exact u8209

def b24590 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 34, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 262 73 152 33 210 146 402), lower := (rows 37 98 262 73 152 33 64 128 256), losses := [] }

theorem u24590 : Upper (D 7) (R 7) [36,96,258,65,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24590 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24591 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 262 73 152 34 209 145 401), lower := (rows 37 98 262 73 152 34 64 128 256), losses := [] }

theorem u24591 : Upper (D 7) (R 7) [36,96,258,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24591 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24592 : Route 9 := (fun mask => (mask,id))

def c24592 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24592 : Upper (D 7) (R 7) [36,96,258,65,136,16] 13 := by
  apply FastRouting.sound _ _ [36,96,258,65,136,16] 13 (by decide) (choices 1) [1,2,128] r24592 c24592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8210
  · exact u8211
  · exact u8212

def r24593 : Route 9 := (fun mask => (mask,id))

def c24593 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24593 : Upper (D 7) (R 7) [36,96,258,65,136,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,65,136,128] 13 (by decide) (choices 1) [1,2,16] r24593 c24593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8213
  · exact u8214
  · exact u8215

def b24594 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 262 88 145 33 202 138 394), lower := (rows 37 98 262 88 145 33 64 128 256), losses := [{ target := 7, region := (rows 5 10 4 8 16 53 64 0 256), good := (rows 37 98 295 122 49 33 64 0 256) }] }

theorem u24594 : Upper (D 7) (R 7) [36,96,258,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24595 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 262 88 145 34 201 137 393), lower := (rows 37 98 262 88 145 34 64 128 256), losses := [] }

theorem u24595 : Upper (D 7) (R 7) [36,96,258,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24596 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 262 88 145 40 195 131 387), lower := (rows 37 98 262 88 145 40 64 128 256), losses := [] }

theorem u24596 : Upper (D 7) (R 7) [36,96,258,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24596 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24597 : Route 9 := (fun mask => (mask,id))

def c24597 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24597 : Upper (D 7) (R 7) [36,96,258,80,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,80,129,128] 13 (by decide) (choices 1) [1,2,8] r24597 c24597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8216
  · exact u8217
  · exact u8218

def r24598 : Route 9 := (fun mask => (mask,id))

def c24598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24598 : Upper (D 7) (R 7) [36,96,258,80,130,1] 13 := by
  apply FastRouting.sound _ _ [36,96,258,80,130,1] 13 (by decide) (choices 1) [1,8,128] r24598 c24598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8219
  · exact u8220
  · exact u8221

def b24599 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 262 88 146 40 193 129 385), lower := (rows 37 98 262 88 146 40 64 128 256), losses := [] }

theorem u24599 : Upper (D 7) (R 7) [36,96,258,80,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24599 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u24599
end Delivery.IrregularNine14.P07
