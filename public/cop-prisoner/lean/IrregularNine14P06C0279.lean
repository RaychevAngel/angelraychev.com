import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0071
import IrregularNine14P06C0072

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16740 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(0,2),(2,6),(3,2)], upper := (rows 11 146 38 104 84 33 325 389 261), lower := (rows 11 146 38 104 84 33 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 24 16 39 64 128 256), good := (rows 43 187 35 104 120 33 64 128 256) }] }

theorem u16740 : Upper (D 6) (R 6) [10,144,34,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16741 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 329, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 11 146 38 104 84 36 321 385 257), lower := (rows 11 146 38 104 84 36 64 128 256), losses := [] }

theorem u16741 : Upper (D 6) (R 6) [10,144,34,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16742 : Route 9 := (fun mask => (mask,id))

def c16742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16742 : Upper (D 6) (R 6) [10,144,34,96,68,256] 13 := by
  apply FastRouting.sound _ _ [10,144,34,96,68,256] 13 (by decide) (choices 1) [1,4] r16742 c16742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4312
  · exact u4313

def b16743 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,0),(3,1)], upper := (rows 11 146 38 104 273 33 68 196 324), lower := (rows 11 146 38 104 273 33 64 128 256), losses := [] }

theorem u16743 : Upper (D 6) (R 6) [10,144,34,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16743 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16744 : Route 9 := (fun mask => (mask,id))

def c16744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16744 : Upper (D 6) (R 6) [10,144,34,96,257,4] 13 := by
  apply FastRouting.sound _ _ [10,144,34,96,257,4] 13 (by decide) (choices 1) [1,4] r16744 c16744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4314
  · exact u4315

def b16745 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 38 104 273 96 69 133 261), lower := (rows 11 146 38 104 273 96 64 128 256), losses := [] }

theorem u16745 : Upper (D 6) (R 6) [10,144,34,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16746 : Route 9 := (fun mask => (mask,id))

def c16746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16746 : Upper (D 6) (R 6) [10,144,34,96,260,1] 13 := by
  apply FastRouting.sound _ _ [10,144,34,96,260,1] 13 (by decide) (choices 1) [1,4] r16746 c16746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4316
  · exact u4317

def b16747 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 11 146 38 104 276 36 65 193 321), lower := (rows 11 146 38 104 276 36 64 128 256), losses := [] }

theorem u16747 : Upper (D 6) (R 6) [10,144,34,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16747 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16748 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 38 104 276 96 69 133 261), lower := (rows 11 146 38 104 276 96 64 128 256), losses := [] }

theorem u16748 : Upper (D 6) (R 6) [10,144,34,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16749 : Route 9 := (fun mask => (mask,id))

def c16749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16749 : Upper (D 6) (R 6) [10,144,34,96,320,1] 13 := by
  apply FastRouting.sound _ _ [10,144,34,96,320,1] 13 (by decide) (choices 1) [1,4] r16749 c16749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4318
  · exact u4319

def r16750 : Route 9 := (fun mask => (mask,id))

def c16750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16750 : Upper (D 6) (R 6) [10,144,34,96,320,4] 13 := by
  apply FastRouting.sound _ _ [10,144,34,96,320,4] 13 (by decide) (choices 1) [1,4] r16750 c16750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4320
  · exact u4321

def b16751 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 0, region := 36, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 146 38 265 81 36 100 228 356), lower := (rows 11 146 38 265 81 36 64 128 256), losses := [] }

theorem u16751 : Upper (D 6) (R 6) [10,144,34,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16752 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 265, targets := 64 },{ cop := 4, region := 166, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 11 146 38 265 81 96 100 164 292), lower := (rows 11 146 38 265 81 96 64 128 256), losses := [] }

theorem u16752 : Upper (D 6) (R 6) [10,144,34,257,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16752 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16753 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 38 265 84 33 100 228 356), lower := (rows 11 146 38 265 84 33 64 128 256), losses := [] }

theorem u16753 : Upper (D 6) (R 6) [10,144,34,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16754 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 329, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 11 146 38 265 84 36 97 225 353), lower := (rows 11 146 38 265 84 36 64 128 256), losses := [] }

theorem u16754 : Upper (D 6) (R 6) [10,144,34,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16755 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 265, targets := 64 }], pairs := [(0,6),(2,0),(3,6)], upper := (rows 11 146 38 265 84 96 101 165 293), lower := (rows 11 146 38 265 84 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 112 64 128 256), good := (rows 14 182 38 264 116 96 96 128 256) }] }

theorem u16755 : Upper (D 6) (R 6) [10,144,34,257,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16755 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16756 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 38 265 112 33 68 196 324), lower := (rows 11 146 38 265 112 33 64 128 256), losses := [] }

theorem u16756 : Upper (D 6) (R 6) [10,144,34,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16757 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 329, targets := 32 }], pairs := [(0,5),(2,0),(2,6)], upper := (rows 11 146 38 265 112 36 69 197 325), lower := (rows 11 146 38 265 112 36 64 128 256), losses := [] }

theorem u16757 : Upper (D 6) (R 6) [10,144,34,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16757 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16758 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 38 265 112 96 69 133 261), lower := (rows 11 146 38 265 112 96 64 128 256), losses := [] }

theorem u16758 : Upper (D 6) (R 6) [10,144,34,257,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16758 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16759 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 146 38 268 21 33 96 224 352), lower := (rows 11 146 38 268 21 33 64 128 256), losses := [] }

theorem u16759 : Upper (D 6) (R 6) [10,144,34,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16760 : Route 9 := (fun mask => (mask,id))

def c16760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16760 : Upper (D 6) (R 6) [10,144,34,260,5,64] 13 := by
  apply FastRouting.sound _ _ [10,144,34,260,5,64] 13 (by decide) (choices 1) [1,32] r16760 c16760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4322
  · exact u4323

def b16761 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 146 38 268 49 33 68 196 324), lower := (rows 11 146 38 268 49 33 64 128 256), losses := [] }

theorem u16761 : Upper (D 6) (R 6) [10,144,34,260,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16762 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 329, targets := 32 }], pairs := [(0,5),(2,6),(4,6)], upper := (rows 11 146 38 268 49 36 65 193 321), lower := (rows 11 146 38 268 49 36 64 128 256), losses := [] }

theorem u16762 : Upper (D 6) (R 6) [10,144,34,260,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16763 : Route 9 := (fun mask => (mask,id))

def c16763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16763 : Upper (D 6) (R 6) [10,144,34,260,33,64] 13 := by
  apply FastRouting.sound _ _ [10,144,34,260,33,64] 13 (by decide) (choices 1) [1,4] r16763 c16763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4324
  · exact u4325

def b16764 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 328, targets := 3 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,0),(3,1)], upper := (rows 11 146 38 268 81 33 100 228 356), lower := (rows 11 146 38 268 81 33 64 128 256), losses := [] }

theorem u16764 : Upper (D 6) (R 6) [10,144,34,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16765 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(4,1)], upper := (rows 11 146 38 268 81 36 97 225 353), lower := (rows 11 146 38 268 81 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 65 129 257), good := (rows 505 144 36 300 465 36 64 128 256) }] }

theorem u16765 : Upper (D 6) (R 6) [10,144,34,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16766 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 265, targets := 64 }], pairs := [(0,6),(2,0),(3,6)], upper := (rows 11 146 38 268 81 96 101 165 293), lower := (rows 11 146 38 268 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 112 64 128 256), good := (rows 14 182 38 268 112 96 96 128 256) }] }

theorem u16766 : Upper (D 6) (R 6) [10,144,34,260,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16767 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 146 38 268 84 33 97 225 353), lower := (rows 11 146 38 268 84 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 33 97 161 289), good := (rows 489 144 508 284 92 481 64 128 256) }] }

theorem u16767 : Upper (D 6) (R 6) [10,144,34,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16768 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 265, targets := 64 }], pairs := [(0,6),(2,0),(3,6)], upper := (rows 11 146 38 268 84 96 97 161 289), lower := (rows 11 146 38 268 84 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 112 64 128 256), good := (rows 14 182 38 268 116 96 96 128 256) }] }

theorem u16768 : Upper (D 6) (R 6) [10,144,34,260,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16769 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 329, targets := 32 },{ cop := 0, region := 36, targets := 64 }], pairs := [(0,5),(2,6),(3,5)], upper := (rows 11 146 38 268 112 33 69 197 325), lower := (rows 11 146 38 268 112 33 64 128 256), losses := [] }

theorem u16769 : Upper (D 6) (R 6) [10,144,34,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16770 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 329, targets := 32 }], pairs := [(0,5),(2,0),(2,6)], upper := (rows 11 146 38 268 112 36 65 193 321), lower := (rows 11 146 38 268 112 36 64 128 256), losses := [] }

theorem u16770 : Upper (D 6) (R 6) [10,144,34,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16771 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 146 38 268 112 96 69 133 261), lower := (rows 11 146 38 268 112 96 64 128 256), losses := [] }

theorem u16771 : Upper (D 6) (R 6) [10,144,34,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16772 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 146 38 296 21 33 68 196 324), lower := (rows 11 146 38 296 21 33 64 128 256), losses := [] }

theorem u16772 : Upper (D 6) (R 6) [10,144,34,288,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16773 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 329, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 146 38 296 21 36 65 193 321), lower := (rows 11 146 38 296 21 36 64 128 256), losses := [] }

theorem u16773 : Upper (D 6) (R 6) [10,144,34,288,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16774 : Route 9 := (fun mask => (mask,id))

def c16774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16774 : Upper (D 6) (R 6) [10,144,34,288,5,64] 13 := by
  apply FastRouting.sound _ _ [10,144,34,288,5,64] 13 (by decide) (choices 1) [1,4] r16774 c16774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4326
  · exact u4327

def b16775 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 328, targets := 3 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,0),(3,1)], upper := (rows 11 146 38 296 81 33 68 196 324), lower := (rows 11 146 38 296 81 33 64 128 256), losses := [] }

theorem u16775 : Upper (D 6) (R 6) [10,144,34,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16776 : Route 9 := (fun mask => (mask,id))

def c16776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16776 : Upper (D 6) (R 6) [10,144,34,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,144,34,288,65,4] 13 (by decide) (choices 1) [1,4] r16776 c16776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4328
  · exact u4329

def b16777 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 265, targets := 64 }], pairs := [(0,6),(2,0),(3,6)], upper := (rows 11 146 38 296 81 96 69 133 261), lower := (rows 11 146 38 296 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 112 64 128 256), good := (rows 14 182 38 296 112 96 96 128 256) }] }

theorem u16777 : Upper (D 6) (R 6) [10,144,34,288,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16778 : Route 9 := (fun mask => (mask,id))

def c16778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16778 : Upper (D 6) (R 6) [10,144,34,288,68,1] 13 := by
  apply FastRouting.sound _ _ [10,144,34,288,68,1] 13 (by decide) (choices 1) [1,4] r16778 c16778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4330
  · exact u4331

def b16779 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 329, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 11 146 38 296 84 36 65 193 321), lower := (rows 11 146 38 296 84 36 64 128 256), losses := [] }

theorem u16779 : Upper (D 6) (R 6) [10,144,34,288,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16780 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 265, targets := 64 }], pairs := [(0,6),(2,0),(3,6)], upper := (rows 11 146 38 296 84 96 69 133 261), lower := (rows 11 146 38 296 84 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 112 64 128 256), good := (rows 14 182 38 296 116 96 96 128 256) }] }

theorem u16780 : Upper (D 6) (R 6) [10,144,34,288,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16780 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16781 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 328, targets := 1 }], pairs := [(2,6),(3,0),(4,6)], upper := (rows 11 146 38 328 21 33 100 228 356), lower := (rows 11 146 38 328 21 33 64 128 256), losses := [] }

theorem u16781 : Upper (D 6) (R 6) [10,144,34,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16782 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 329, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 146 38 328 21 36 97 225 353), lower := (rows 11 146 38 328 21 36 64 128 256), losses := [] }

theorem u16782 : Upper (D 6) (R 6) [10,144,34,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16783 : Route 9 := (fun mask => (mask,id))

def c16783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16783 : Upper (D 6) (R 6) [10,144,34,320,5,64] 13 := by
  apply FastRouting.sound _ _ [10,144,34,320,5,64] 13 (by decide) (choices 1) [1,4,32] r16783 c16783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4332
  · exact u4333
  · exact u4334

def b16784 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 146 38 328 49 33 68 196 324), lower := (rows 11 146 38 328 49 33 64 128 256), losses := [] }

theorem u16784 : Upper (D 6) (R 6) [10,144,34,320,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16784 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16785 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 2, region := 329, targets := 32 }], pairs := [(0,5),(2,6),(4,6)], upper := (rows 11 146 38 328 49 36 69 197 325), lower := (rows 11 146 38 328 49 36 64 128 256), losses := [] }

theorem u16785 : Upper (D 6) (R 6) [10,144,34,320,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16786 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 329, targets := 32 },{ cop := 4, region := 134, targets := 64 }], pairs := [(0,5),(1,6),(3,5)], upper := (rows 11 146 38 328 49 96 69 133 261), lower := (rows 11 146 38 328 49 96 64 128 256), losses := [] }

theorem u16786 : Upper (D 6) (R 6) [10,144,34,320,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16787 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 328, targets := 3 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 146 38 328 81 33 100 164 292), lower := (rows 11 146 38 328 81 33 64 128 256), losses := [] }

theorem u16787 : Upper (D 6) (R 6) [10,144,34,320,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16787 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16788 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 146 38 328 81 36 101 165 293), lower := (rows 11 146 38 328 81 36 64 128 256), losses := [] }

theorem u16788 : Upper (D 6) (R 6) [10,144,34,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16788 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16789 : Route 9 := (fun mask => (mask,id))

def c16789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16789 : Upper (D 6) (R 6) [10,144,34,320,68,1] 13 := by
  apply FastRouting.sound _ _ [10,144,34,320,68,1] 13 (by decide) (choices 1) [1,4,32] r16789 c16789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4335
  · exact u4336
  · exact u4337

def b16790 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 2, region := 329, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 11 146 38 328 84 36 97 161 289), lower := (rows 11 146 38 328 84 36 64 128 256), losses := [] }

theorem u16790 : Upper (D 6) (R 6) [10,144,34,320,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16791 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 454, targets := 1 }], pairs := [(1,0),(4,2),(4,6)], upper := (rows 11 146 100 13 49 34 324 452 324), lower := (rows 11 146 100 13 49 34 64 128 256), losses := [] }

theorem u16791 : Upper (D 6) (R 6) [10,144,96,5,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16792 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 4, region := 450, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 146 100 13 49 36 322 450 322), lower := (rows 11 146 100 13 49 36 64 128 256), losses := [] }

theorem u16792 : Upper (D 6) (R 6) [10,144,96,5,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16792 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16793 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 13 49 96 326 390 262), lower := (rows 11 146 100 13 49 96 64 128 256), losses := [] }

theorem u16793 : Upper (D 6) (R 6) [10,144,96,5,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16794 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 146 100 13 49 288 70 198 326), lower := (rows 11 146 100 13 49 288 64 128 256), losses := [] }

theorem u16794 : Upper (D 6) (R 6) [10,144,96,5,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16794 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16795 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 146 100 13 50 33 324 452 324), lower := (rows 11 146 100 13 50 33 64 128 256), losses := [] }

theorem u16795 : Upper (D 6) (R 6) [10,144,96,5,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16796 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 146 100 13 50 36 321 449 321), lower := (rows 11 146 100 13 50 36 64 128 256), losses := [] }

theorem u16796 : Upper (D 6) (R 6) [10,144,96,5,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16797 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 146 100 13 50 96 325 389 261), lower := (rows 11 146 100 13 50 96 64 128 256), losses := [] }

theorem u16797 : Upper (D 6) (R 6) [10,144,96,5,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16798 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 364, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 11 146 100 13 50 288 69 197 325), lower := (rows 11 146 100 13 50 288 64 128 256), losses := [] }

theorem u16798 : Upper (D 6) (R 6) [10,144,96,5,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16798 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16799 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 5, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 146 100 13 273 34 100 228 356), lower := (rows 11 146 100 13 273 34 64 128 256), losses := [] }

theorem u16799 : Upper (D 6) (R 6) [10,144,96,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u16799
end Delivery.IrregularNine14.P06
