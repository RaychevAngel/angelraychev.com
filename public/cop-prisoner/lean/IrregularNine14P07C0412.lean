import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0138
import IrregularNine14P07C0139

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r24720 : Route 9 := (fun mask => (mask,id))

def c24720 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24720 : Upper (D 7) (R 7) [36,96,320,3,136,128] 13 := by
  apply FastRouting.sound _ _ [36,96,320,3,136,128] 13 (by decide) (choices 1) [1,2,16] r24720 c24720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8323
  · exact u8324
  · exact u8325

def b24721 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 98 324 25 26 33 194 130 386), lower := (rows 37 98 324 25 26 33 64 128 256), losses := [] }

theorem u24721 : Upper (D 7) (R 7) [36,96,320,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24722 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 59, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 37 98 324 25 26 34 193 129 385), lower := (rows 37 98 324 25 26 34 64 128 256), losses := [] }

theorem u24722 : Upper (D 7) (R 7) [36,96,320,17,10,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24723 : Route 9 := (fun mask => (mask,id))

def c24723 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24723 : Upper (D 7) (R 7) [36,96,320,17,10,128] 13 := by
  apply FastRouting.sound _ _ [36,96,320,17,10,128] 13 (by decide) (choices 1) [1,2,128] r24723 c24723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8326
  · exact u8327
  · exact u8328

def b24724 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 324 25 146 33 202 138 394), lower := (rows 37 98 324 25 146 33 64 128 256), losses := [] }

theorem u24724 : Upper (D 7) (R 7) [36,96,320,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24725 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 3, region := 452, targets := 34 }], pairs := [(0,7),(1,7),(2,1),(2,5)], upper := (rows 37 98 324 25 146 34 201 137 393), lower := (rows 37 98 324 25 146 34 64 128 256), losses := [] }

theorem u24725 : Upper (D 7) (R 7) [36,96,320,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24725 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24726 : Route 9 := (fun mask => (mask,id))

def c24726 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24726 : Upper (D 7) (R 7) [36,96,320,17,130,8] 13 := by
  apply FastRouting.sound _ _ [36,96,320,17,130,8] 13 (by decide) (choices 1) [1,2,128] r24726 c24726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8329
  · exact u8330
  · exact u8331

def r24727 : Route 9 := (fun mask => (mask,id))

def c24727 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24727 : Upper (D 7) (R 7) [36,96,320,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,320,17,130,128] 13 (by decide) (choices 1) [1,2,8] r24727 c24727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8332
  · exact u8333
  · exact u8334

def b24728 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(1,0),(2,0)], upper := (rows 37 98 324 25 152 33 194 130 386), lower := (rows 37 98 324 25 152 33 64 128 256), losses := [] }

theorem u24728 : Upper (D 7) (R 7) [36,96,320,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24729 : Route 9 := (fun mask => (mask,id))

def c24729 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24729 : Upper (D 7) (R 7) [36,96,320,17,136,2] 13 := by
  apply FastRouting.sound _ _ [36,96,320,17,136,2] 13 (by decide) (choices 1) [1,2,128] r24729 c24729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8335
  · exact u8336
  · exact u8337

def r24730 : Route 9 := (fun mask => (mask,id))

def c24730 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24730 : Upper (D 7) (R 7) [36,96,320,17,136,128] 13 := by
  apply FastRouting.sound _ _ [36,96,320,17,136,128] 13 (by decide) (choices 1) [1,2] r24730 c24730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8338
  · exact u8339

def b24731 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 324 26 145 33 202 138 394), lower := (rows 37 98 324 26 145 33 64 128 256), losses := [] }

theorem u24731 : Upper (D 7) (R 7) [36,96,320,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24732 : Route 9 := (fun mask => (mask,id))

def c24732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24732 : Upper (D 7) (R 7) [36,96,320,18,129,2] 13 := by
  apply FastRouting.sound _ _ [36,96,320,18,129,2] 13 (by decide) (choices 1) [1,8,128] r24732 c24732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8340
  · exact u8341
  · exact u8342

def r24733 : Route 9 := (fun mask => (mask,id))

def c24733 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u24733 : Upper (D 7) (R 7) [36,96,320,18,129,8] 13 := by
  apply FastRouting.sound _ _ [36,96,320,18,129,8] 13 (by decide) (choices 1) [1,2,128] r24733 c24733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8343
  · exact u8344
  · exact u8345

def r24734 : Route 9 := (fun mask => (mask,id))

def c24734 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24734 : Upper (D 7) (R 7) [36,96,320,18,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,320,18,129,128] 13 (by decide) (choices 1) [1,2,8] r24734 c24734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8346
  · exact u8347
  · exact u8348

def b24735 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 324 26 152 33 195 131 387), lower := (rows 37 98 324 26 152 33 64 128 256), losses := [] }

theorem u24735 : Upper (D 7) (R 7) [36,96,320,18,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24736 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(2,1),(2,5)], upper := (rows 37 98 324 26 152 34 193 129 385), lower := (rows 37 98 324 26 152 34 64 128 256), losses := [] }

theorem u24736 : Upper (D 7) (R 7) [36,96,320,18,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24737 : Route 9 := (fun mask => (mask,id))

def c24737 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24737 : Upper (D 7) (R 7) [36,96,320,18,136,128] 13 := by
  apply FastRouting.sound _ _ [36,96,320,18,136,128] 13 (by decide) (choices 1) [1,2] r24737 c24737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8349
  · exact u8350

def b24738 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 324 137 146 33 90 154 282), lower := (rows 37 98 324 137 146 33 64 128 256), losses := [] }

theorem u24738 : Upper (D 7) (R 7) [36,96,320,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24739 : Route 9 := (fun mask => (mask,id))

def c24739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24739 : Upper (D 7) (R 7) [36,96,320,129,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,320,129,130,2] 13 (by decide) (choices 1) [1,8,16] r24739 c24739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8351
  · exact u8352
  · exact u8353

def r24740 : Route 9 := (fun mask => (mask,id))

def c24740 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24740 : Upper (D 7) (R 7) [36,96,320,129,130,8] 13 := by
  apply FastRouting.sound _ _ [36,96,320,129,130,8] 13 (by decide) (choices 1) [1,2,16] r24740 c24740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8354
  · exact u8355
  · exact u8356

def r24741 : Route 9 := (fun mask => (mask,id))

def c24741 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24741 : Upper (D 7) (R 7) [36,96,320,129,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,320,129,130,16] 13 (by decide) (choices 1) [1,2,8] r24741 c24741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8357
  · exact u8358
  · exact u8359

def b24742 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 388 11 81 34 216 152 408), lower := (rows 37 98 388 11 81 34 64 128 256), losses := [] }

theorem u24742 : Upper (D 7) (R 7) [36,96,384,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24743 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 468, targets := 32 },{ cop := 4, region := 42, targets := 128 }], pairs := [(1,7),(2,5),(4,5)], upper := (rows 37 98 388 11 81 40 210 146 402), lower := (rows 37 98 388 11 81 40 64 128 256), losses := [] }

theorem u24743 : Upper (D 7) (R 7) [36,96,384,3,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24743 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24744 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 388 11 81 48 202 138 394), lower := (rows 37 98 388 11 81 48 64 128 256), losses := [] }

theorem u24744 : Upper (D 7) (R 7) [36,96,384,3,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24744 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24745 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 388 11 81 160 90 154 282), lower := (rows 37 98 388 11 81 160 64 128 256), losses := [] }

theorem u24745 : Upper (D 7) (R 7) [36,96,384,3,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24746 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 388 11 88 33 210 146 402), lower := (rows 37 98 388 11 88 33 64 128 256), losses := [] }

theorem u24746 : Upper (D 7) (R 7) [36,96,384,3,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24747 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 388 11 88 34 209 145 401), lower := (rows 37 98 388 11 88 34 64 128 256), losses := [] }

theorem u24747 : Upper (D 7) (R 7) [36,96,384,3,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24748 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 388 11 88 48 195 131 387), lower := (rows 37 98 388 11 88 48 64 128 256), losses := [] }

theorem u24748 : Upper (D 7) (R 7) [36,96,384,3,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24748 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24749 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 388 11 88 160 83 147 275), lower := (rows 37 98 388 11 88 160 64 128 256), losses := [] }

theorem u24749 : Upper (D 7) (R 7) [36,96,384,3,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24750 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 388 11 146 33 88 216 344), lower := (rows 37 98 388 11 146 33 64 128 256), losses := [] }

theorem u24750 : Upper (D 7) (R 7) [36,96,384,3,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24751 : Route 9 := (fun mask => (mask,id))

def c24751 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24751 : Upper (D 7) (R 7) [36,96,384,3,130,8] 13 := by
  apply FastRouting.sound _ _ [36,96,384,3,130,8] 13 (by decide) (choices 1) [1,16] r24751 c24751
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8360
  · exact u8361

def b24752 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 452, targets := 32 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 388 11 146 48 73 201 329), lower := (rows 37 98 388 11 146 48 64 128 256), losses := [] }

theorem u24752 : Upper (D 7) (R 7) [36,96,384,3,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24752 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24753 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 388 11 146 96 89 153 281), lower := (rows 37 98 388 11 146 96 64 128 256), losses := [] }

theorem u24753 : Upper (D 7) (R 7) [36,96,384,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24754 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 388 11 152 33 82 210 338), lower := (rows 37 98 388 11 152 33 64 128 256), losses := [] }

theorem u24754 : Upper (D 7) (R 7) [36,96,384,3,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24755 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 388 11 152 34 81 209 337), lower := (rows 37 98 388 11 152 34 64 128 256), losses := [] }

theorem u24755 : Upper (D 7) (R 7) [36,96,384,3,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24756 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 452, targets := 32 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 388 11 152 48 67 195 323), lower := (rows 37 98 388 11 152 48 64 128 256), losses := [] }

theorem u24756 : Upper (D 7) (R 7) [36,96,384,3,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24756 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24757 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 388 11 152 96 83 147 275), lower := (rows 37 98 388 11 152 96 64 128 256), losses := [] }

theorem u24757 : Upper (D 7) (R 7) [36,96,384,3,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24758 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 98 388 11 208 33 90 154 282), lower := (rows 37 98 388 11 208 33 64 128 256), losses := [] }

theorem u24758 : Upper (D 7) (R 7) [36,96,384,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24759 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 98 388 11 208 34 89 153 281), lower := (rows 37 98 388 11 208 34 64 128 256), losses := [] }

theorem u24759 : Upper (D 7) (R 7) [36,96,384,3,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24760 : Route 9 := (fun mask => (mask,id))

def c24760 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24760 : Upper (D 7) (R 7) [36,96,384,3,192,8] 13 := by
  apply FastRouting.sound _ _ [36,96,384,3,192,8] 13 (by decide) (choices 1) [1,2,16] r24760 c24760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8362
  · exact u8363
  · exact u8364

def b24761 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 388 11 208 48 75 139 267), lower := (rows 37 98 388 11 208 48 64 128 256), losses := [] }

theorem u24761 : Upper (D 7) (R 7) [36,96,384,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24761 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24762 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 388 25 26 33 194 194 450), lower := (rows 37 98 388 25 26 33 64 128 256), losses := [] }

theorem u24762 : Upper (D 7) (R 7) [36,96,384,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24763 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 37 98 388 25 26 34 193 193 449), lower := (rows 37 98 388 25 26 34 64 128 256), losses := [] }

theorem u24763 : Upper (D 7) (R 7) [36,96,384,17,10,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24764 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 388 25 26 96 195 131 387), lower := (rows 37 98 388 25 26 96 64 128 256), losses := [] }

theorem u24764 : Upper (D 7) (R 7) [36,96,384,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24765 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 388 25 26 160 67 195 323), lower := (rows 37 98 388 25 26 160 64 128 256), losses := [] }

theorem u24765 : Upper (D 7) (R 7) [36,96,384,17,10,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24766 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 388 25 88 33 194 130 386), lower := (rows 37 98 388 25 88 33 64 128 256), losses := [] }

theorem u24766 : Upper (D 7) (R 7) [36,96,384,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24767 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 4, region := 34, targets := 129 }], pairs := [(0,6),(1,0),(1,7),(2,6)], upper := (rows 37 98 388 25 88 34 195 131 387), lower := (rows 37 98 388 25 88 34 64 128 256), losses := [] }

theorem u24767 : Upper (D 7) (R 7) [36,96,384,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24768 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 98 388 25 88 160 67 131 259), lower := (rows 37 98 388 25 88 160 64 128 256), losses := [] }

theorem u24768 : Upper (D 7) (R 7) [36,96,384,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24769 : PairBound 9 := { available := 74, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 98, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 388 25 146 33 74 202 330), lower := (rows 37 98 388 25 146 33 64 128 256), losses := [] }

theorem u24769 : Upper (D 7) (R 7) [36,96,384,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24770 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 452, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 37 98 388 25 146 34 73 201 329), lower := (rows 37 98 388 25 146 34 64 128 256), losses := [] }

theorem u24770 : Upper (D 7) (R 7) [36,96,384,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24771 : Route 9 := (fun mask => (mask,id))

def c24771 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24771 : Upper (D 7) (R 7) [36,96,384,17,130,8] 13 := by
  apply FastRouting.sound _ _ [36,96,384,17,130,8] 13 (by decide) (choices 1) [1,2] r24771 c24771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8365
  · exact u8366

def b24772 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 388 25 146 96 75 139 267), lower := (rows 37 98 388 25 146 96 64 128 256), losses := [] }

theorem u24772 : Upper (D 7) (R 7) [36,96,384,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24773 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 57, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 98 388 25 152 33 66 194 322), lower := (rows 37 98 388 25 152 33 64 128 256), losses := [] }

theorem u24773 : Upper (D 7) (R 7) [36,96,384,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24774 : Route 9 := (fun mask => (mask,id))

def c24774 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24774 : Upper (D 7) (R 7) [36,96,384,17,136,2] 13 := by
  apply FastRouting.sound _ _ [36,96,384,17,136,2] 13 (by decide) (choices 1) [1,2] r24774 c24774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8367
  · exact u8368

def b24775 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 388 25 152 96 67 131 259), lower := (rows 37 98 388 25 152 96 64 128 256), losses := [] }

theorem u24775 : Upper (D 7) (R 7) [36,96,384,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24776 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 98, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 388 25 208 33 74 138 266), lower := (rows 37 98 388 25 208 33 64 128 256), losses := [] }

theorem u24776 : Upper (D 7) (R 7) [36,96,384,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r24777 : Route 9 := (fun mask => (mask,id))

def c24777 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24777 : Upper (D 7) (R 7) [36,96,384,17,192,2] 13 := by
  apply FastRouting.sound _ _ [36,96,384,17,192,2] 13 (by decide) (choices 1) [1,2,8] r24777 c24777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8369
  · exact u8370
  · exact u8371

def b24778 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 389, targets := 64 },{ cop := 0, region := 66, targets := 128 }], pairs := [(0,6),(1,7),(2,6)], upper := (rows 37 98 388 25 208 40 67 131 259), lower := (rows 37 98 388 25 208 40 64 128 256), losses := [] }

theorem u24778 : Upper (D 7) (R 7) [36,96,384,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24778 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24779 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 388, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(2,0)], upper := (rows 37 98 388 26 81 33 202 138 394), lower := (rows 37 98 388 26 81 33 64 128 256), losses := [] }

theorem u24779 : Upper (D 7) (R 7) [36,96,384,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u24779
end Delivery.IrregularNine14.P07
