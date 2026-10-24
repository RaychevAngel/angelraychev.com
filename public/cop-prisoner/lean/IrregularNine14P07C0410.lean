import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0137
import IrregularNine14P07C0138

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r24600 : Route 9 := (fun mask => (mask,id))

def c24600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24600 : Upper (D 7) (R 7) [36,96,258,80,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,258,80,130,128] 13 (by decide) (choices 1) [1,8] r24600 c24600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8222
  · exact u8223

def b24601 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 2, region := 33, targets := 130 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 98 262 88 152 33 195 131 387), lower := (rows 37 98 262 88 152 33 64 128 256), losses := [] }

theorem u24601 : Upper (D 7) (R 7) [36,96,258,80,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24602 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 262 88 152 34 193 129 385), lower := (rows 37 98 262 88 152 34 64 128 256), losses := [] }

theorem u24602 : Upper (D 7) (R 7) [36,96,258,80,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24603 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 1, region := 261, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 37 98 262 88 152 160 67 131 259), lower := (rows 37 98 262 88 152 160 64 128 256), losses := [] }

theorem u24603 : Upper (D 7) (R 7) [36,96,258,80,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24604 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 98 262 137 146 33 88 216 344), lower := (rows 37 98 262 137 146 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 22 41 22 0 67 131 259), good := (rows 477 478 470 457 470 457 64 128 256) }] }

theorem u24604 : Upper (D 7) (R 7) [36,96,258,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24604 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24605 : Route 9 := (fun mask => (mask,id))

def c24605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24605 : Upper (D 7) (R 7) [36,96,258,129,130,8] 13 := by
  apply FastRouting.sound _ _ [36,96,258,129,130,8] 13 (by decide) (choices 1) [1,16] r24605 c24605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8224
  · exact u8225

def r24606 : Route 9 := (fun mask => (mask,id))

def c24606 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24606 : Upper (D 7) (R 7) [36,96,258,129,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,258,129,130,16] 13 (by decide) (choices 1) [1,8] r24606 c24606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8226
  · exact u8227

def b24607 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 262 137 146 96 89 153 281), lower := (rows 37 98 262 137 146 96 64 128 256), losses := [] }

theorem u24607 : Upper (D 7) (R 7) [36,96,258,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24607 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24608 : Route 9 := (fun mask => (mask,id))

def c24608 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24608 : Upper (D 7) (R 7) [36,96,258,129,192,1] 13 := by
  apply FastRouting.sound _ _ [36,96,258,129,192,1] 13 (by decide) (choices 1) [2,8,16] r24608 c24608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8228
  · exact u8229
  · exact u8230

def b24609 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 37 98 262 137 208 34 89 153 281), lower := (rows 37 98 262 137 208 34 64 128 256), losses := [] }

theorem u24609 : Upper (D 7) (R 7) [36,96,258,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24609 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24610 : Route 9 := (fun mask => (mask,id))

def c24610 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24610 : Upper (D 7) (R 7) [36,96,258,129,192,8] 13 := by
  apply FastRouting.sound _ _ [36,96,258,129,192,8] 13 (by decide) (choices 1) [1,2,16] r24610 c24610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8231
  · exact u8232
  · exact u8233

def b24611 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 262 137 208 48 75 139 267), lower := (rows 37 98 262 137 208 48 64 128 256), losses := [] }

theorem u24611 : Upper (D 7) (R 7) [36,96,258,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24611 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24612 : Route 9 := (fun mask => (mask,id))

def c24612 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24612 : Upper (D 7) (R 7) [36,96,258,130,192,1] 13 := by
  apply FastRouting.sound _ _ [36,96,258,130,192,1] 13 (by decide) (choices 1) [1,8,16] r24612 c24612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8234
  · exact u8235
  · exact u8236

def b24613 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 4, region := 42, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 37 98 262 138 208 40 81 145 273), lower := (rows 37 98 262 138 208 40 64 128 256), losses := [] }

theorem u24613 : Upper (D 7) (R 7) [36,96,258,130,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24613 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24614 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 262 138 208 48 73 137 265), lower := (rows 37 98 262 138 208 48 64 128 256), losses := [] }

theorem u24614 : Upper (D 7) (R 7) [36,96,258,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24614 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24615 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 268 11 81 34 208 144 400), lower := (rows 37 98 268 11 81 34 64 128 256), losses := [] }

theorem u24615 : Upper (D 7) (R 7) [36,96,264,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24616 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 268 11 81 48 194 130 386), lower := (rows 37 98 268 11 81 48 64 128 256), losses := [] }

theorem u24616 : Upper (D 7) (R 7) [36,96,264,3,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24616 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24617 : Route 9 := (fun mask => (mask,id))

def c24617 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24617 : Upper (D 7) (R 7) [36,96,264,3,65,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,3,65,128] 13 (by decide) (choices 1) [2,16,128] r24617 c24617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8237
  · exact u8238
  · exact u8239

def b24618 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 268 11 145 34 208 208 464), lower := (rows 37 98 268 11 145 34 64 128 256), losses := [] }

theorem u24618 : Upper (D 7) (R 7) [36,96,264,3,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24619 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 0, region := 194, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 37 98 268 11 145 48 194 194 450), lower := (rows 37 98 268 11 145 48 64 128 256), losses := [] }

theorem u24619 : Upper (D 7) (R 7) [36,96,264,3,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24619 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24620 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 268 11 145 96 210 146 402), lower := (rows 37 98 268 11 145 96 64 128 256), losses := [] }

theorem u24620 : Upper (D 7) (R 7) [36,96,264,3,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24621 : Route 9 := (fun mask => (mask,id))

def c24621 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24621 : Upper (D 7) (R 7) [36,96,264,3,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,3,129,128] 13 (by decide) (choices 1) [2,16] r24621 c24621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8240
  · exact u8241

def b24622 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 268 11 146 33 208 208 464), lower := (rows 37 98 268 11 146 33 64 128 256), losses := [] }

theorem u24622 : Upper (D 7) (R 7) [36,96,264,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24623 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 3, region := 452, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 37 98 268 11 146 48 193 193 449), lower := (rows 37 98 268 11 146 48 64 128 256), losses := [] }

theorem u24623 : Upper (D 7) (R 7) [36,96,264,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24623 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24624 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 268 11 146 96 209 145 401), lower := (rows 37 98 268 11 146 96 64 128 256), losses := [] }

theorem u24624 : Upper (D 7) (R 7) [36,96,264,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24625 : Route 9 := (fun mask => (mask,id))

def c24625 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24625 : Upper (D 7) (R 7) [36,96,264,3,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,3,130,128] 13 (by decide) (choices 1) [1,16] r24625 c24625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8242
  · exact u8243

def b24626 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 268 11 208 33 210 146 402), lower := (rows 37 98 268 11 208 33 64 128 256), losses := [] }

theorem u24626 : Upper (D 7) (R 7) [36,96,264,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24627 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 268 11 208 34 209 145 401), lower := (rows 37 98 268 11 208 34 64 128 256), losses := [] }

theorem u24627 : Upper (D 7) (R 7) [36,96,264,3,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24628 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 268 11 208 48 195 131 387), lower := (rows 37 98 268 11 208 48 64 128 256), losses := [] }

theorem u24628 : Upper (D 7) (R 7) [36,96,264,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24628 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24629 : Route 9 := (fun mask => (mask,id))

def c24629 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24629 : Upper (D 7) (R 7) [36,96,264,3,192,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,3,192,128] 13 (by decide) (choices 1) [1,2,16] r24629 c24629
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8244
  · exact u8245
  · exact u8246

def b24630 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 268 25 146 33 194 194 450), lower := (rows 37 98 268 25 146 33 64 128 256), losses := [] }

theorem u24630 : Upper (D 7) (R 7) [36,96,264,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24631 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 452, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 37 98 268 25 146 34 193 193 449), lower := (rows 37 98 268 25 146 34 64 128 256), losses := [] }

theorem u24631 : Upper (D 7) (R 7) [36,96,264,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24632 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 268 25 146 96 195 131 387), lower := (rows 37 98 268 25 146 96 64 128 256), losses := [] }

theorem u24632 : Upper (D 7) (R 7) [36,96,264,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24633 : Route 9 := (fun mask => (mask,id))

def c24633 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24633 : Upper (D 7) (R 7) [36,96,264,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,17,130,128] 13 (by decide) (choices 1) [1,2] r24633 c24633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8247
  · exact u8248

def b24634 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 268 25 208 33 194 130 386), lower := (rows 37 98 268 25 208 33 64 128 256), losses := [] }

theorem u24634 : Upper (D 7) (R 7) [36,96,264,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24635 : Route 9 := (fun mask => (mask,id))

def c24635 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24635 : Upper (D 7) (R 7) [36,96,264,17,192,2] 13 := by
  apply FastRouting.sound _ _ [36,96,264,17,192,2] 13 (by decide) (choices 1) [1,2,128] r24635 c24635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8249
  · exact u8250
  · exact u8251

def r24636 : Route 9 := (fun mask => (mask,id))

def c24636 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24636 : Upper (D 7) (R 7) [36,96,264,17,192,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,17,192,128] 13 (by decide) (choices 1) [1,2] r24636 c24636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8252
  · exact u8253

def b24637 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 388, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 98 268 26 81 33 194 130 386), lower := (rows 37 98 268 26 81 33 64 128 256), losses := [] }

theorem u24637 : Upper (D 7) (R 7) [36,96,264,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24638 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 98 268 26 81 34 193 129 385), lower := (rows 37 98 268 26 81 34 64 128 256), losses := [] }

theorem u24638 : Upper (D 7) (R 7) [36,96,264,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24639 : Route 9 := (fun mask => (mask,id))

def c24639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24639 : Upper (D 7) (R 7) [36,96,264,18,65,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,18,65,128] 13 (by decide) (choices 1) [1,2,128] r24639 c24639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8254
  · exact u8255
  · exact u8256

def b24640 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 452, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 98 268 26 145 33 194 194 450), lower := (rows 37 98 268 26 145 33 64 128 256), losses := [] }

theorem u24640 : Upper (D 7) (R 7) [36,96,264,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24641 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 37 98 268 26 145 34 193 193 449), lower := (rows 37 98 268 26 145 34 64 128 256), losses := [] }

theorem u24641 : Upper (D 7) (R 7) [36,96,264,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24642 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 268 26 145 96 195 131 387), lower := (rows 37 98 268 26 145 96 64 128 256), losses := [] }

theorem u24642 : Upper (D 7) (R 7) [36,96,264,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24643 : Route 9 := (fun mask => (mask,id))

def c24643 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24643 : Upper (D 7) (R 7) [36,96,264,18,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,18,129,128] 13 (by decide) (choices 1) [1,2] r24643 c24643
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8257
  · exact u8258

def b24644 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 98 268 26 208 33 195 131 387), lower := (rows 37 98 268 26 208 33 64 128 256), losses := [] }

theorem u24644 : Upper (D 7) (R 7) [36,96,264,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24645 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 37 98 268 26 208 34 193 129 385), lower := (rows 37 98 268 26 208 34 64 128 256), losses := [] }

theorem u24645 : Upper (D 7) (R 7) [36,96,264,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24646 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 42, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 37 98 268 26 208 160 67 131 259), lower := (rows 37 98 268 26 208 160 64 128 256), losses := [] }

theorem u24646 : Upper (D 7) (R 7) [36,96,264,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24647 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 37 98 268 73 19 34 208 144 400), lower := (rows 37 98 268 73 19 34 64 128 256), losses := [] }

theorem u24647 : Upper (D 7) (R 7) [36,96,264,65,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24648 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 50, targets := 128 },{ cop := 4, region := 460, targets := 32 }], pairs := [(1,7),(2,5),(4,7)], upper := (rows 37 98 268 73 19 48 194 130 386), lower := (rows 37 98 268 73 19 48 64 128 256), losses := [] }

theorem u24648 : Upper (D 7) (R 7) [36,96,264,65,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24648 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24649 : Route 9 := (fun mask => (mask,id))

def c24649 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24649 : Upper (D 7) (R 7) [36,96,264,65,3,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,65,3,128] 13 (by decide) (choices 1) [2,16,128] r24649 c24649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8259
  · exact u8260
  · exact u8261

def r24650 : Route 9 := (fun mask => (mask,id))

def c24650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24650 : Upper (D 7) (R 7) [36,96,264,65,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,264,65,129,2] 13 (by decide) (choices 1) [2,16,128] r24650 c24650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8262
  · exact u8263
  · exact u8264

def r24651 : Route 9 := (fun mask => (mask,id))

def c24651 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24651 : Upper (D 7) (R 7) [36,96,264,65,129,16] 13 := by
  apply FastRouting.sound _ _ [36,96,264,65,129,16] 13 (by decide) (choices 1) [2,128] r24651 c24651
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8265
  · exact u8266

def r24652 : Route 9 := (fun mask => (mask,id))

def c24652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24652 : Upper (D 7) (R 7) [36,96,264,65,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,65,129,128] 13 (by decide) (choices 1) [2,16] r24652 c24652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8267
  · exact u8268

def b24653 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 210, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 268 73 146 33 210 146 402), lower := (rows 37 98 268 73 146 33 64 128 256), losses := [] }

theorem u24653 : Upper (D 7) (R 7) [36,96,264,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24654 : Route 9 := (fun mask => (mask,id))

def c24654 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24654 : Upper (D 7) (R 7) [36,96,264,65,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,264,65,130,2] 13 (by decide) (choices 1) [1,16,128] r24654 c24654
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8269
  · exact u8270
  · exact u8271

def r24655 : Route 9 := (fun mask => (mask,id))

def c24655 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24655 : Upper (D 7) (R 7) [36,96,264,65,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,264,65,130,16] 13 (by decide) (choices 1) [1,2,128] r24655 c24655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8272
  · exact u8273
  · exact u8274

def r24656 : Route 9 := (fun mask => (mask,id))

def c24656 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24656 : Upper (D 7) (R 7) [36,96,264,65,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,65,130,128] 13 (by decide) (choices 1) [1,2,16] r24656 c24656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8275
  · exact u8276
  · exact u8277

def b24657 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 268 88 145 33 194 130 386), lower := (rows 37 98 268 88 145 33 64 128 256), losses := [] }

theorem u24657 : Upper (D 7) (R 7) [36,96,264,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24658 : Route 9 := (fun mask => (mask,id))

def c24658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24658 : Upper (D 7) (R 7) [36,96,264,80,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,264,80,129,2] 13 (by decide) (choices 1) [1,2,128] r24658 c24658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8278
  · exact u8279
  · exact u8280

def b24659 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,7)], upper := (rows 37 98 268 88 145 160 67 131 259), lower := (rows 37 98 268 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 36 98 270 122 176 160 64 160 256) },{ target := 7, region := (rows 1 3 28 24 16 32 81 0 273), good := (rows 359 98 268 348 351 32 64 0 256) }] }

theorem u24659 : Upper (D 7) (R 7) [36,96,264,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u24659
end Delivery.IrregularNine14.P07
