import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0046
import IrregularNine14P06C0047

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13560 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 134 56 81 288 69 197 325), lower := (rows 11 38 134 56 81 288 64 128 256), losses := [] }

theorem u13560 : Upper (D 6) (R 6) [10,36,130,48,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13560 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13561 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 134 56 84 33 321 449 321), lower := (rows 11 38 134 56 84 33 64 128 256), losses := [] }

theorem u13561 : Upper (D 6) (R 6) [10,36,130,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13562 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 134 56 84 96 321 385 257), lower := (rows 11 38 134 56 84 96 64 128 256), losses := [] }

theorem u13562 : Upper (D 6) (R 6) [10,36,130,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13563 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 134 56 84 288 65 193 321), lower := (rows 11 38 134 56 84 288 64 128 256), losses := [] }

theorem u13563 : Upper (D 6) (R 6) [10,36,130,48,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13563 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13564 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 38 134 56 273 33 68 196 324), lower := (rows 11 38 134 56 273 33 64 128 256), losses := [] }

theorem u13564 : Upper (D 6) (R 6) [10,36,130,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13565 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 56 273 36 65 193 321), lower := (rows 11 38 134 56 273 36 64 128 256), losses := [] }

theorem u13565 : Upper (D 6) (R 6) [10,36,130,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13566 : Route 9 := (fun mask => (mask,id))

def c13566 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13566 : Upper (D 6) (R 6) [10,36,130,48,257,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,48,257,64] 13 (by decide) (choices 1) [1,4] r13566 c13566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2801
  · exact u2802

def b13567 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 134 56 276 33 65 193 321), lower := (rows 11 38 134 56 276 33 64 128 256), losses := [] }

theorem u13567 : Upper (D 6) (R 6) [10,36,130,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13568 : Route 9 := (fun mask => (mask,id))

def c13568 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13568 : Upper (D 6) (R 6) [10,36,130,48,260,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,48,260,64] 13 (by decide) (choices 1) [1] r13568 c13568
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u2803

def r13569 : Route 9 := (fun mask => (mask,id))

def c13569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13569 : Upper (D 6) (R 6) [10,36,130,48,320,1] 13 := by
  apply FastRouting.sound _ _ [10,36,130,48,320,1] 13 (by decide) (choices 1) [1,4] r13569 c13569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2804
  · exact u2805

def b13570 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 56 336 36 65 193 321), lower := (rows 11 38 134 56 336 36 64 128 256), losses := [] }

theorem u13570 : Upper (D 6) (R 6) [10,36,130,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13571 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 134 56 336 96 69 133 261), lower := (rows 11 38 134 56 336 96 64 128 256), losses := [] }

theorem u13571 : Upper (D 6) (R 6) [10,36,130,48,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13572 : PairBound 9 := { available := 336, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 73 49 36 336 464 336), lower := (rows 11 38 134 73 49 36 64 128 256), losses := [] }

theorem u13572 : Upper (D 6) (R 6) [10,36,130,65,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13573 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 134 73 49 48 324 452 324), lower := (rows 11 38 134 73 49 48 64 128 256), losses := [] }

theorem u13573 : Upper (D 6) (R 6) [10,36,130,65,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13573 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13574 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 48, targets := 6 },{ cop := 4, region := 390, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 134 73 49 96 340 404 276), lower := (rows 11 38 134 73 49 96 64 128 256), losses := [] }

theorem u13574 : Upper (D 6) (R 6) [10,36,130,65,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13574 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13575 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 134 73 49 288 84 212 340), lower := (rows 11 38 134 73 49 288 64 128 256), losses := [] }

theorem u13575 : Upper (D 6) (R 6) [10,36,130,65,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13575 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13576 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 73 84 33 368 432 304), lower := (rows 11 38 134 73 84 33 64 128 256), losses := [] }

theorem u13576 : Upper (D 6) (R 6) [10,36,130,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13577 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 134 73 84 48 353 417 289), lower := (rows 11 38 134 73 84 48 64 128 256), losses := [] }

theorem u13577 : Upper (D 6) (R 6) [10,36,130,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13577 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13578 : Route 9 := (fun mask => (mask,id))

def c13578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13578 : Upper (D 6) (R 6) [10,36,130,65,68,256] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,68,256] 13 (by decide) (choices 1) [1,16,32] r13578 c13578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2806
  · exact u2807
  · exact u2808

def b13579 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 73 112 33 340 404 276), lower := (rows 11 38 134 73 112 33 64 128 256), losses := [] }

theorem u13579 : Upper (D 6) (R 6) [10,36,130,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13580 : PairBound 9 := { available := 273, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 73 112 36 337 401 273), lower := (rows 11 38 134 73 112 36 64 128 256), losses := [] }

theorem u13580 : Upper (D 6) (R 6) [10,36,130,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13581 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 134 73 112 48 325 389 261), lower := (rows 11 38 134 73 112 48 64 128 256), losses := [] }

theorem u13581 : Upper (D 6) (R 6) [10,36,130,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13581 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13582 : Route 9 := (fun mask => (mask,id))

def c13582 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13582 : Upper (D 6) (R 6) [10,36,130,65,96,256] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,96,256] 13 (by decide) (choices 1) [1,4,16] r13582 c13582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2809
  · exact u2810
  · exact u2811

def b13583 : PairBound 9 := { available := 112, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 73 273 36 112 240 368), lower := (rows 11 38 134 73 273 36 64 128 256), losses := [] }

theorem u13583 : Upper (D 6) (R 6) [10,36,130,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13584 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 38 134 73 273 48 100 228 356), lower := (rows 11 38 134 73 273 48 64 128 256), losses := [] }

theorem u13584 : Upper (D 6) (R 6) [10,36,130,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13584 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13585 : Route 9 := (fun mask => (mask,id))

def c13585 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13585 : Upper (D 6) (R 6) [10,36,130,65,257,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,257,64] 13 (by decide) (choices 1) [4,16,32] r13585 c13585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2812
  · exact u2813
  · exact u2814

def b13586 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 73 276 33 112 240 368), lower := (rows 11 38 134 73 276 33 64 128 256), losses := [] }

theorem u13586 : Upper (D 6) (R 6) [10,36,130,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13587 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 134 73 276 48 97 225 353), lower := (rows 11 38 134 73 276 48 64 128 256), losses := [] }

theorem u13587 : Upper (D 6) (R 6) [10,36,130,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13587 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13588 : Route 9 := (fun mask => (mask,id))

def c13588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13588 : Upper (D 6) (R 6) [10,36,130,65,260,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,260,64] 13 (by decide) (choices 1) [1,16,32] r13588 c13588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2815
  · exact u2816
  · exact u2817

def b13589 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 73 304 33 84 212 340), lower := (rows 11 38 134 73 304 33 64 128 256), losses := [] }

theorem u13589 : Upper (D 6) (R 6) [10,36,130,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13590 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 73 304 36 81 209 337), lower := (rows 11 38 134 73 304 36 64 128 256), losses := [] }

theorem u13590 : Upper (D 6) (R 6) [10,36,130,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13591 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 134 73 304 48 69 197 325), lower := (rows 11 38 134 73 304 48 64 128 256), losses := [] }

theorem u13591 : Upper (D 6) (R 6) [10,36,130,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13591 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13592 : Route 9 := (fun mask => (mask,id))

def c13592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13592 : Upper (D 6) (R 6) [10,36,130,65,288,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,288,64] 13 (by decide) (choices 1) [1,4,16] r13592 c13592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2818
  · exact u2819
  · exact u2820

def b13593 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 134 73 336 33 116 180 308), lower := (rows 11 38 134 73 336 33 64 128 256), losses := [] }

theorem u13593 : Upper (D 6) (R 6) [10,36,130,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13594 : PairBound 9 := { available := 49, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 73 336 36 113 177 305), lower := (rows 11 38 134 73 336 36 64 128 256), losses := [] }

theorem u13594 : Upper (D 6) (R 6) [10,36,130,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13595 : Route 9 := (fun mask => (mask,id))

def c13595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13595 : Upper (D 6) (R 6) [10,36,130,65,320,16] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,320,16] 13 (by decide) (choices 1) [1,4,32] r13595 c13595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2821
  · exact u2822
  · exact u2823

def b13596 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 38 134 76 49 33 336 464 336), lower := (rows 11 38 134 76 49 33 64 128 256), losses := [] }

theorem u13596 : Upper (D 6) (R 6) [10,36,130,68,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13597 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 134 76 49 48 321 449 321), lower := (rows 11 38 134 76 49 48 64 128 256), losses := [] }

theorem u13597 : Upper (D 6) (R 6) [10,36,130,68,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13597 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13598 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 4, region := 390, targets := 64 }], pairs := [(1,6),(4,1),(4,2)], upper := (rows 11 38 134 76 49 96 337 401 273), lower := (rows 11 38 134 76 49 96 64 128 256), losses := [] }

theorem u13598 : Upper (D 6) (R 6) [10,36,130,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13599 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 134 76 49 288 81 209 337), lower := (rows 11 38 134 76 49 288 64 128 256), losses := [] }

theorem u13599 : Upper (D 6) (R 6) [10,36,130,68,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13599 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13600 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 134 76 112 33 337 401 273), lower := (rows 11 38 134 76 112 33 64 128 256), losses := [] }

theorem u13600 : Upper (D 6) (R 6) [10,36,130,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13601 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 134 76 112 48 321 385 257), lower := (rows 11 38 134 76 112 48 64 128 256), losses := [] }

theorem u13601 : Upper (D 6) (R 6) [10,36,130,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13601 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13602 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 134 76 112 288 81 145 273), lower := (rows 11 38 134 76 112 288 64 128 256), losses := [] }

theorem u13602 : Upper (D 6) (R 6) [10,36,130,68,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13602 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13603 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 134 76 273 33 112 240 368), lower := (rows 11 38 134 76 273 33 64 128 256), losses := [] }

theorem u13603 : Upper (D 6) (R 6) [10,36,130,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13604 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 134 76 273 48 97 225 353), lower := (rows 11 38 134 76 273 48 64 128 256), losses := [] }

theorem u13604 : Upper (D 6) (R 6) [10,36,130,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13604 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13605 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 134 76 273 96 113 177 305), lower := (rows 11 38 134 76 273 96 64 128 256), losses := [] }

theorem u13605 : Upper (D 6) (R 6) [10,36,130,68,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13606 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 134 76 304 33 81 209 337), lower := (rows 11 38 134 76 304 33 64 128 256), losses := [] }

theorem u13606 : Upper (D 6) (R 6) [10,36,130,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13607 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 38 134 76 304 48 65 193 321), lower := (rows 11 38 134 76 304 48 64 128 256), losses := [] }

theorem u13607 : Upper (D 6) (R 6) [10,36,130,68,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13607 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13608 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 38 134 76 304 96 81 145 273), lower := (rows 11 38 134 76 304 96 64 128 256), losses := [] }

theorem u13608 : Upper (D 6) (R 6) [10,36,130,68,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13609 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 134 76 336 33 113 177 305), lower := (rows 11 38 134 76 336 33 64 128 256), losses := [] }

theorem u13609 : Upper (D 6) (R 6) [10,36,130,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13610 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 134 76 336 48 97 161 289), lower := (rows 11 38 134 76 336 48 64 128 256), losses := [] }

theorem u13610 : Upper (D 6) (R 6) [10,36,130,68,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13610 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13611 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 360, targets := 6 },{ cop := 5, region := 454, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 38 134 88 21 33 352 480 352), lower := (rows 11 38 134 88 21 33 64 128 256), losses := [] }

theorem u13611 : Upper (D 6) (R 6) [10,36,130,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13612 : Route 9 := (fun mask => (mask,id))

def c13612 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u13612 : Upper (D 6) (R 6) [10,36,130,80,5,64] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,5,64] 13 (by decide) (choices 1) [1,32,256] r13612 c13612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2824
  · exact u2825
  · exact u2826

def b13613 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 360, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 38 134 88 21 288 97 225 353), lower := (rows 11 38 134 88 21 288 64 128 256), losses := [] }

theorem u13613 : Upper (D 6) (R 6) [10,36,130,80,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13613 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13614 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 134 88 49 33 324 452 324), lower := (rows 11 38 134 88 49 33 64 128 256), losses := [] }

theorem u13614 : Upper (D 6) (R 6) [10,36,130,80,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13615 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 88 49 36 321 449 321), lower := (rows 11 38 134 88 49 36 64 128 256), losses := [] }

theorem u13615 : Upper (D 6) (R 6) [10,36,130,80,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13616 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 390, targets := 64 },{ cop := 0, region := 388, targets := 32 }], pairs := [(1,6),(2,5),(2,6)], upper := (rows 11 38 134 88 49 96 325 389 261), lower := (rows 11 38 134 88 49 96 64 128 256), losses := [] }

theorem u13616 : Upper (D 6) (R 6) [10,36,130,80,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13617 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 11 38 134 88 49 288 69 197 325), lower := (rows 11 38 134 88 49 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 24 16 0 81 145 273), good := (rows 463 6 134 472 477 256 64 128 256) }] }

theorem u13617 : Upper (D 6) (R 6) [10,36,130,80,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13617 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13618 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 134 88 273 33 100 228 356), lower := (rows 11 38 134 88 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 17 49 66 130 258), good := (rows 505 484 452 120 313 57 64 128 256) }] }

theorem u13618 : Upper (D 6) (R 6) [10,36,130,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13619 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 134 88 273 36 97 225 353), lower := (rows 11 38 134 88 273 36 64 128 256), losses := [] }

theorem u13619 : Upper (D 6) (R 6) [10,36,130,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13619
end Delivery.IrregularNine14.P06
