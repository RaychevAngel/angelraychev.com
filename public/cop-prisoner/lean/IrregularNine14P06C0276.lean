import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0070
import IrregularNine14P06C0071

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16560 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 292 41 84 34 81 209 337), lower := (rows 11 134 292 41 84 34 64 128 256), losses := [] }

theorem u16560 : Upper (D 6) (R 6) [10,132,288,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16561 : Route 9 := (fun mask => (mask,id))

def c16561 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16561 : Upper (D 6) (R 6) [10,132,288,33,68,16] 13 := by
  apply FastRouting.sound _ _ [10,132,288,33,68,16] 13 (by decide) (choices 1) [1,2] r16561 c16561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4218
  · exact u4219

def r16562 : Route 9 := (fun mask => (mask,id))

def c16562 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16562 : Upper (D 6) (R 6) [10,132,288,33,68,64] 13 := by
  apply FastRouting.sound _ _ [10,132,288,33,68,64] 13 (by decide) (choices 1) [1,2,16] r16562 c16562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4220
  · exact u4221
  · exact u4222

def b16563 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 134 292 56 81 33 70 198 326), lower := (rows 11 134 292 56 81 33 64 128 256), losses := [] }

theorem u16563 : Upper (D 6) (R 6) [10,132,288,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16563 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16564 : PairBound 9 := { available := 69, camps := [], pairs := [(3,0),(3,2),(3,6)], upper := (rows 11 134 292 56 81 34 69 197 325), lower := (rows 11 134 292 56 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 64 128 256), good := (rows 42 166 292 56 120 34 64 128 256) },{ target := 2, region := (rows 1 2 0 24 16 35 64 128 256), good := (rows 43 162 288 56 121 34 64 128 256) },{ target := 6, region := (rows 1 2 4 24 16 35 0 128 256), good := (rows 43 166 292 56 57 34 0 128 256) }] }

theorem u16564 : Upper (D 6) (R 6) [10,132,288,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16564 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16565 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 292 56 81 36 67 195 323), lower := (rows 11 134 292 56 81 36 64 128 256), losses := [] }

theorem u16565 : Upper (D 6) (R 6) [10,132,288,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16566 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 292 56 81 96 71 135 263), lower := (rows 11 134 292 56 81 96 64 128 256), losses := [] }

theorem u16566 : Upper (D 6) (R 6) [10,132,288,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16567 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 292 56 82 33 69 197 325), lower := (rows 11 134 292 56 82 33 64 128 256), losses := [] }

theorem u16567 : Upper (D 6) (R 6) [10,132,288,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16568 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 292 56 82 36 65 193 321), lower := (rows 11 134 292 56 82 36 64 128 256), losses := [] }

theorem u16568 : Upper (D 6) (R 6) [10,132,288,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16569 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 292 56 82 96 69 133 261), lower := (rows 11 134 292 56 82 96 64 128 256), losses := [] }

theorem u16569 : Upper (D 6) (R 6) [10,132,288,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16570 : Route 9 := (fun mask => (mask,id))

def c16570 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16570 : Upper (D 6) (R 6) [10,132,288,48,68,1] 13 := by
  apply FastRouting.sound _ _ [10,132,288,48,68,1] 13 (by decide) (choices 1) [1,2] r16570 c16570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4223
  · exact u4224

def r16571 : Route 9 := (fun mask => (mask,id))

def c16571 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16571 : Upper (D 6) (R 6) [10,132,288,48,68,2] 13 := by
  apply FastRouting.sound _ _ [10,132,288,48,68,2] 13 (by decide) (choices 1) [1] r16571 c16571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u4225

def b16572 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 292 56 84 96 67 131 259), lower := (rows 11 134 292 56 84 96 64 128 256), losses := [] }

theorem u16572 : Upper (D 6) (R 6) [10,132,288,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16573 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(1,0),(2,0),(3,2)], upper := (rows 11 134 292 73 21 34 112 240 368), lower := (rows 11 134 292 73 21 34 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 35 80 144 272), good := (rows 43 162 288 105 505 34 64 128 256) }] }

theorem u16573 : Upper (D 6) (R 6) [10,132,288,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16574 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 134 292 73 21 48 98 226 354), lower := (rows 11 134 292 73 21 48 64 128 256), losses := [] }

theorem u16574 : Upper (D 6) (R 6) [10,132,288,65,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16574 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16575 : Route 9 := (fun mask => (mask,id))

def c16575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16575 : Upper (D 6) (R 6) [10,132,288,65,5,64] 13 := by
  apply FastRouting.sound _ _ [10,132,288,65,5,64] 13 (by decide) (choices 1) [2,16,32] r16575 c16575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4226
  · exact u4227
  · exact u4228

def b16576 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 454, targets := 1 }], pairs := [(1,0),(4,2),(4,6)], upper := (rows 11 134 292 73 49 34 84 212 340), lower := (rows 11 134 292 73 49 34 64 128 256), losses := [] }

theorem u16576 : Upper (D 6) (R 6) [10,132,288,65,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16577 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 292 73 49 36 82 210 338), lower := (rows 11 134 292 73 49 36 64 128 256), losses := [] }

theorem u16577 : Upper (D 6) (R 6) [10,132,288,65,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16578 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 292 73 49 48 70 198 326), lower := (rows 11 134 292 73 49 48 64 128 256), losses := [] }

theorem u16578 : Upper (D 6) (R 6) [10,132,288,65,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16578 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16579 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 48, targets := 6 },{ cop := 4, region := 390, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 134 292 73 49 96 86 150 278), lower := (rows 11 134 292 73 49 96 64 128 256), losses := [] }

theorem u16579 : Upper (D 6) (R 6) [10,132,288,65,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16580 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 292 73 50 33 84 212 340), lower := (rows 11 134 292 73 50 33 64 128 256), losses := [] }

theorem u16580 : Upper (D 6) (R 6) [10,132,288,65,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16581 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 292 73 50 36 81 209 337), lower := (rows 11 134 292 73 50 36 64 128 256), losses := [] }

theorem u16581 : Upper (D 6) (R 6) [10,132,288,65,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16582 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 134 292 73 50 48 69 197 325), lower := (rows 11 134 292 73 50 48 64 128 256), losses := [] }

theorem u16582 : Upper (D 6) (R 6) [10,132,288,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16582 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16583 : Route 9 := (fun mask => (mask,id))

def c16583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16583 : Upper (D 6) (R 6) [10,132,288,65,34,64] 13 := by
  apply FastRouting.sound _ _ [10,132,288,65,34,64] 13 (by decide) (choices 1) [1,4,16] r16583 c16583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4229
  · exact u4230
  · exact u4231

def b16584 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 292 73 84 33 114 178 306), lower := (rows 11 134 292 73 84 33 64 128 256), losses := [] }

theorem u16584 : Upper (D 6) (R 6) [10,132,288,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16585 : Route 9 := (fun mask => (mask,id))

def c16585 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16585 : Upper (D 6) (R 6) [10,132,288,65,68,2] 13 := by
  apply FastRouting.sound _ _ [10,132,288,65,68,2] 13 (by decide) (choices 1) [1,16,32] r16585 c16585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4232
  · exact u4233
  · exact u4234

def r16586 : Route 9 := (fun mask => (mask,id))

def c16586 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16586 : Upper (D 6) (R 6) [10,132,288,65,68,16] 13 := by
  apply FastRouting.sound _ _ [10,132,288,65,68,16] 13 (by decide) (choices 1) [1,2,32] r16586 c16586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4235
  · exact u4236
  · exact u4237

def b16587 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 292 73 112 33 86 150 278), lower := (rows 11 134 292 73 112 33 64 128 256), losses := [] }

theorem u16587 : Upper (D 6) (R 6) [10,132,288,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16588 : Route 9 := (fun mask => (mask,id))

def c16588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16588 : Upper (D 6) (R 6) [10,132,288,65,96,2] 13 := by
  apply FastRouting.sound _ _ [10,132,288,65,96,2] 13 (by decide) (choices 1) [1,4,16] r16588 c16588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4238
  · exact u4239
  · exact u4240

def b16589 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 292 73 112 36 83 147 275), lower := (rows 11 134 292 73 112 36 64 128 256), losses := [] }

theorem u16589 : Upper (D 6) (R 6) [10,132,288,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16590 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 292 73 112 48 71 135 263), lower := (rows 11 134 292 73 112 48 64 128 256), losses := [] }

theorem u16590 : Upper (D 6) (R 6) [10,132,288,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16590 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16591 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 292 76 49 33 82 210 338), lower := (rows 11 134 292 76 49 33 64 128 256), losses := [] }

theorem u16591 : Upper (D 6) (R 6) [10,132,288,68,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16592 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 332, targets := 2 },{ cop := 0, region := 48, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 134 292 76 49 34 81 209 337), lower := (rows 11 134 292 76 49 34 64 128 256), losses := [] }

theorem u16592 : Upper (D 6) (R 6) [10,132,288,68,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16593 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 292 76 49 48 67 195 323), lower := (rows 11 134 292 76 49 48 64 128 256), losses := [] }

theorem u16593 : Upper (D 6) (R 6) [10,132,288,68,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16593 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16594 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 390, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,6),(2,6),(4,2)], upper := (rows 11 134 292 76 49 96 83 147 275), lower := (rows 11 134 292 76 49 96 64 128 256), losses := [] }

theorem u16594 : Upper (D 6) (R 6) [10,132,288,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16595 : Route 9 := (fun mask => (mask,id))

def c16595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16595 : Upper (D 6) (R 6) [10,132,288,68,34,1] 13 := by
  apply FastRouting.sound _ _ [10,132,288,68,34,1] 13 (by decide) (choices 1) [1,16] r16595 c16595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4241
  · exact u4242

def b16596 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 134 292 76 50 48 65 193 321), lower := (rows 11 134 292 76 50 48 64 128 256), losses := [] }

theorem u16596 : Upper (D 6) (R 6) [10,132,288,68,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16596 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16597 : Route 9 := (fun mask => (mask,id))

def c16597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16597 : Upper (D 6) (R 6) [10,132,288,68,34,64] 13 := by
  apply FastRouting.sound _ _ [10,132,288,68,34,64] 13 (by decide) (choices 1) [1,16] r16597 c16597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4243
  · exact u4244

def r16598 : Route 9 := (fun mask => (mask,id))

def c16598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16598 : Upper (D 6) (R 6) [10,132,288,68,66,1] 13 := by
  apply FastRouting.sound _ _ [10,132,288,68,66,1] 13 (by decide) (choices 1) [1,16,32] r16598 c16598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4245
  · exact u4246
  · exact u4247

def r16599 : Route 9 := (fun mask => (mask,id))

def c16599 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16599 : Upper (D 6) (R 6) [10,132,288,68,66,16] 13 := by
  apply FastRouting.sound _ _ [10,132,288,68,66,16] 13 (by decide) (choices 1) [1,32] r16599 c16599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4248
  · exact u4249

def r16600 : Route 9 := (fun mask => (mask,id))

def c16600 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16600 : Upper (D 6) (R 6) [10,132,288,68,96,1] 13 := by
  apply FastRouting.sound _ _ [10,132,288,68,96,1] 13 (by decide) (choices 1) [1,2,16] r16600 c16600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4250
  · exact u4251
  · exact u4252

def r16601 : Route 9 := (fun mask => (mask,id))

def c16601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16601 : Upper (D 6) (R 6) [10,132,288,68,96,2] 13 := by
  apply FastRouting.sound _ _ [10,132,288,68,96,2] 13 (by decide) (choices 1) [1,16] r16601 c16601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4253
  · exact u4254

def b16602 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 203, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 292 76 112 48 67 131 259), lower := (rows 11 134 292 76 112 48 64 128 256), losses := [] }

theorem u16602 : Upper (D 6) (R 6) [10,132,288,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16602 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16603 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 454, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 134 292 88 21 33 98 226 354), lower := (rows 11 134 292 88 21 33 64 128 256), losses := [{ target := 0, region := (rows 0 54 36 24 16 32 100 164 292), good := (rows 10 454 486 90 478 486 64 128 256) }] }

theorem u16603 : Upper (D 6) (R 6) [10,132,288,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16604 : Route 9 := (fun mask => (mask,id))

def c16604 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16604 : Upper (D 6) (R 6) [10,132,288,80,5,2] 13 := by
  apply FastRouting.sound _ _ [10,132,288,80,5,2] 13 (by decide) (choices 1) [1,32] r16604 c16604
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4255
  · exact u4256

def r16605 : Route 9 := (fun mask => (mask,id))

def c16605 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16605 : Upper (D 6) (R 6) [10,132,288,80,5,64] 13 := by
  apply FastRouting.sound _ _ [10,132,288,80,5,64] 13 (by decide) (choices 1) [1,2,32] r16605 c16605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4257
  · exact u4258
  · exact u4259

def b16606 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 134 292 88 49 33 70 198 326), lower := (rows 11 134 292 88 49 33 64 128 256), losses := [] }

theorem u16606 : Upper (D 6) (R 6) [10,132,288,80,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16607 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 324, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 11 134 292 88 49 34 69 197 325), lower := (rows 11 134 292 88 49 34 64 128 256), losses := [] }

theorem u16607 : Upper (D 6) (R 6) [10,132,288,80,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16608 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 292 88 49 36 67 195 323), lower := (rows 11 134 292 88 49 36 64 128 256), losses := [] }

theorem u16608 : Upper (D 6) (R 6) [10,132,288,80,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16609 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 390, targets := 64 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 134 292 88 49 96 71 135 263), lower := (rows 11 134 292 88 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 104 64 128 256), good := (rows 57 132 292 120 49 96 96 128 256) }] }

theorem u16609 : Upper (D 6) (R 6) [10,132,288,80,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16610 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 11 134 292 88 50 33 69 197 325), lower := (rows 11 134 292 88 50 33 64 128 256), losses := [] }

theorem u16610 : Upper (D 6) (R 6) [10,132,288,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16611 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 292 88 50 36 65 193 321), lower := (rows 11 134 292 88 50 36 64 128 256), losses := [] }

theorem u16611 : Upper (D 6) (R 6) [10,132,288,80,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16612 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(4,0),(4,2)], upper := (rows 11 134 292 88 50 96 69 133 261), lower := (rows 11 134 292 88 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 104 64 128 256), good := (rows 58 134 292 120 50 96 96 128 256) },{ target := 2, region := (rows 1 2 0 8 17 104 64 128 256), good := (rows 59 130 288 120 50 96 96 128 256) }] }

theorem u16612 : Upper (D 6) (R 6) [10,132,288,80,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16613 : Route 9 := (fun mask => (mask,id))

def c16613 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16613 : Upper (D 6) (R 6) [10,132,288,96,5,1] 13 := by
  apply FastRouting.sound _ _ [10,132,288,96,5,1] 13 (by decide) (choices 1) [2,16] r16613 c16613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4260
  · exact u4261

def r16614 : Route 9 := (fun mask => (mask,id))

def c16614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16614 : Upper (D 6) (R 6) [10,132,288,96,5,2] 13 := by
  apply FastRouting.sound _ _ [10,132,288,96,5,2] 13 (by decide) (choices 1) [1,16] r16614 c16614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4262
  · exact u4263

def b16615 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(3,2)], upper := (rows 11 134 292 104 21 48 67 195 323), lower := (rows 11 134 292 104 21 48 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 48 65 129 257), good := (rows 459 130 288 104 505 56 64 128 256) }] }

theorem u16615 : Upper (D 6) (R 6) [10,132,288,96,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16615 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16616 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 292 104 21 96 83 147 275), lower := (rows 11 134 292 104 21 96 64 128 256), losses := [] }

theorem u16616 : Upper (D 6) (R 6) [10,132,288,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16616 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16617 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 40, targets := 6 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(3,1),(3,2)], upper := (rows 11 134 292 104 81 33 86 150 278), lower := (rows 11 134 292 104 81 33 64 128 256), losses := [] }

theorem u16617 : Upper (D 6) (R 6) [10,132,288,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16618 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 11 134 292 104 81 34 85 149 277), lower := (rows 11 134 292 104 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 35 64 128 256), good := (rows 42 166 292 104 120 34 64 128 256) }] }

theorem u16618 : Upper (D 6) (R 6) [10,132,288,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16619 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 134 292 104 81 36 83 147 275), lower := (rows 11 134 292 104 81 36 64 128 256), losses := [] }

theorem u16619 : Upper (D 6) (R 6) [10,132,288,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16619 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u16619
end Delivery.IrregularNine14.P06
