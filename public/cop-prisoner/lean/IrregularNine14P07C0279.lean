import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0064
import IrregularNine14P07C0065

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16740 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 22 168 81 34 449 385 385), lower := (rows 13 98 22 168 81 34 64 128 256), losses := [] }

theorem u16740 : Upper (D 7) (R 7) [12,96,18,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16741 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 22 168 81 160 323 387 259), lower := (rows 13 98 22 168 81 160 64 128 256), losses := [] }

theorem u16741 : Upper (D 7) (R 7) [12,96,18,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16742 : Route 9 := (fun mask => (mask,id))

def c16742 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16742 : Upper (D 7) (R 7) [12,96,18,160,65,256] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,65,256] 13 (by decide) (choices 1) [1,2,128] r16742 c16742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3885
  · exact u3886
  · exact u3887

def b16743 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 40, targets := 66 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,7),(2,7),(3,1),(3,6)], upper := (rows 13 98 22 168 145 33 322 450 322), lower := (rows 13 98 22 168 145 33 64 128 256), losses := [] }

theorem u16743 : Upper (D 7) (R 7) [12,96,18,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16744 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,7),(2,7),(4,1),(4,5)], upper := (rows 13 98 22 168 145 34 321 449 321), lower := (rows 13 98 22 168 145 34 64 128 256), losses := [] }

theorem u16744 : Upper (D 7) (R 7) [12,96,18,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16745 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 168 145 96 323 387 259), lower := (rows 13 98 22 168 145 96 64 128 256), losses := [] }

theorem u16745 : Upper (D 7) (R 7) [12,96,18,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16746 : Route 9 := (fun mask => (mask,id))

def c16746 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16746 : Upper (D 7) (R 7) [12,96,18,160,129,256] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,129,256] 13 (by decide) (choices 1) [1,2] r16746 c16746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3888
  · exact u3889

def r16747 : Route 9 := (fun mask => (mask,id))

def c16747 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u16747 : Upper (D 7) (R 7) [12,96,18,160,192,1] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,192,1] 13 (by decide) (choices 1) [1,2,256] r16747 c16747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3890
  · exact u3891
  · exact u3892

def b16748 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 46, targets := 1 },{ cop := 0, region := 464, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 13 98 22 168 208 34 321 385 257), lower := (rows 13 98 22 168 208 34 64 128 256), losses := [] }

theorem u16748 : Upper (D 7) (R 7) [12,96,18,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16749 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 0, region := 354, targets := 128 }], pairs := [(0,6),(1,7),(3,6)], upper := (rows 13 98 22 168 208 288 67 131 259), lower := (rows 13 98 22 168 208 288 64 128 256), losses := [] }

theorem u16749 : Upper (D 7) (R 7) [12,96,18,160,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16749 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16750 : Route 9 := (fun mask => (mask,id))

def c16750 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16750 : Upper (D 7) (R 7) [12,96,18,160,257,1] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,257,1] 13 (by decide) (choices 1) [2,128] r16750 c16750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3893
  · exact u3894

def b16751 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 98 22 168 273 34 193 193 449), lower := (rows 13 98 22 168 273 34 64 128 256), losses := [] }

theorem u16751 : Upper (D 7) (R 7) [12,96,18,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16752 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 168 273 96 195 131 387), lower := (rows 13 98 22 168 273 96 64 128 256), losses := [] }

theorem u16752 : Upper (D 7) (R 7) [12,96,18,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16753 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 22 168 273 160 67 195 323), lower := (rows 13 98 22 168 273 160 64 128 256), losses := [] }

theorem u16753 : Upper (D 7) (R 7) [12,96,18,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16754 : Route 9 := (fun mask => (mask,id))

def c16754 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16754 : Upper (D 7) (R 7) [12,96,18,160,320,1] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,320,1] 13 (by decide) (choices 1) [1,2,128] r16754 c16754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3895
  · exact u3896
  · exact u3897

def b16755 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 22 168 336 34 193 129 385), lower := (rows 13 98 22 168 336 34 64 128 256), losses := [] }

theorem u16755 : Upper (D 7) (R 7) [12,96,18,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16756 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 22 168 336 160 67 131 259), lower := (rows 13 98 22 168 336 160 64 128 256), losses := [] }

theorem u16756 : Upper (D 7) (R 7) [12,96,18,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16757 : Route 9 := (fun mask => (mask,id))

def c16757 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16757 : Upper (D 7) (R 7) [12,96,18,160,384,1] 13 := by
  apply FastRouting.sound _ _ [12,96,18,160,384,1] 13 (by decide) (choices 1) [1,2] r16757 c16757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3898
  · exact u3899

def b16758 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 98 22 168 400 34 65 193 321), lower := (rows 13 98 22 168 400 34 64 128 256), losses := [] }

theorem u16758 : Upper (D 7) (R 7) [12,96,18,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16759 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 168 400 96 67 131 259), lower := (rows 13 98 22 168 400 96 64 128 256), losses := [] }

theorem u16759 : Upper (D 7) (R 7) [12,96,18,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16760 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(2,0)], upper := (rows 13 98 22 265 145 34 224 224 480), lower := (rows 13 98 22 265 145 34 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 20 32 98 162 290), good := (rows 29 480 477 265 145 480 64 128 256) }] }

theorem u16760 : Upper (D 7) (R 7) [12,96,18,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16761 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 265 145 96 226 162 418), lower := (rows 13 98 22 265 145 96 64 128 256), losses := [] }

theorem u16761 : Upper (D 7) (R 7) [12,96,18,257,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16762 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 5, region := 66, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(2,0)], upper := (rows 13 98 22 265 145 160 98 226 354), lower := (rows 13 98 22 265 145 160 64 128 256), losses := [{ target := 7, region := (rows 5 34 4 12 16 32 98 0 290), good := (rows 13 354 351 265 17 354 64 0 256) }] }

theorem u16762 : Upper (D 7) (R 7) [12,96,18,257,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16763 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 214, targets := 1 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(1,0),(2,0),(4,0)], upper := (rows 13 98 22 265 176 33 194 194 450), lower := (rows 13 98 22 265 176 33 64 128 256), losses := [] }

theorem u16763 : Upper (D 7) (R 7) [12,96,18,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16764 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 22 265 176 34 193 193 449), lower := (rows 13 98 22 265 176 34 64 128 256), losses := [] }

theorem u16764 : Upper (D 7) (R 7) [12,96,18,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16765 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 265 176 96 195 131 387), lower := (rows 13 98 22 265 176 96 64 128 256), losses := [] }

theorem u16765 : Upper (D 7) (R 7) [12,96,18,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16766 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 22 265 176 160 67 195 323), lower := (rows 13 98 22 265 176 160 64 128 256), losses := [] }

theorem u16766 : Upper (D 7) (R 7) [12,96,18,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16767 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 22 266 49 33 192 192 448), lower := (rows 13 98 22 266 49 33 64 128 256), losses := [] }

theorem u16767 : Upper (D 7) (R 7) [12,96,18,258,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16768 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 266 49 96 193 129 385), lower := (rows 13 98 22 266 49 96 64 128 256), losses := [] }

theorem u16768 : Upper (D 7) (R 7) [12,96,18,258,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16769 : Route 9 := (fun mask => (mask,id))

def c16769 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16769 : Upper (D 7) (R 7) [12,96,18,258,33,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,258,33,128] 13 (by decide) (choices 1) [1,128] r16769 c16769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3900
  · exact u3901

def r16770 : Route 9 := (fun mask => (mask,id))

def c16770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16770 : Upper (D 7) (R 7) [12,96,18,258,129,1] 13 := by
  apply FastRouting.sound _ _ [12,96,18,258,129,1] 13 (by decide) (choices 1) [32,128] r16770 c16770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3902
  · exact u3903

def b16771 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 266 145 96 225 161 417), lower := (rows 13 98 22 266 145 96 64 128 256), losses := [] }

theorem u16771 : Upper (D 7) (R 7) [12,96,18,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16772_1 : Upper (D 7) (R 7) [12,96,18,258,129,128,1] 13 :=
  permutation_upper _ _ _ [12,96,18,258,129,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3903

theorem m16772_32 : Upper (D 7) (R 7) [12,96,18,258,129,128,32] 13 :=
  permutation_upper _ _ _ [12,96,18,258,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3904

def r16772 : Route 9 := (fun mask => (mask,id))

def c16772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16772 : Upper (D 7) (R 7) [12,96,18,258,129,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,258,129,128] 13 (by decide) (choices 1) [1,32] r16772 c16772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16772_1
  · exact m16772_32

def r16773 : Route 9 := (fun mask => (mask,id))

def c16773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16773 : Upper (D 7) (R 7) [12,96,18,258,160,1] 13 := by
  apply FastRouting.sound _ _ [12,96,18,258,160,1] 13 (by decide) (choices 1) [1,128] r16773 c16773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3905
  · exact u3906

def b16774 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 266 176 96 193 129 385), lower := (rows 13 98 22 266 176 96 64 128 256), losses := [] }

theorem u16774 : Upper (D 7) (R 7) [12,96,18,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16775 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 22 266 176 160 65 193 321), lower := (rows 13 98 22 266 176 160 64 128 256), losses := [] }

theorem u16775 : Upper (D 7) (R 7) [12,96,18,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16776 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 4, region := 38, targets := 128 }], pairs := [(0,6),(1,7),(2,7),(3,6)], upper := (rows 13 98 22 296 81 33 194 130 386), lower := (rows 13 98 22 296 81 33 64 128 256), losses := [] }

theorem u16776 : Upper (D 7) (R 7) [12,96,18,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16777 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 22 296 81 34 193 129 385), lower := (rows 13 98 22 296 81 34 64 128 256), losses := [] }

theorem u16777 : Upper (D 7) (R 7) [12,96,18,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16778 : Route 9 := (fun mask => (mask,id))

def c16778 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16778 : Upper (D 7) (R 7) [12,96,18,288,65,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,288,65,128] 13 (by decide) (choices 1) [1,2,128] r16778 c16778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3907
  · exact u3908
  · exact u3909

def r16779 : Route 9 := (fun mask => (mask,id))

def c16779 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16779 : Upper (D 7) (R 7) [12,96,18,288,129,1] 13 := by
  apply FastRouting.sound _ _ [12,96,18,288,129,1] 13 (by decide) (choices 1) [2,128] r16779 c16779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3910
  · exact u3911

def b16780 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 98 22 296 145 34 193 193 449), lower := (rows 13 98 22 296 145 34 64 128 256), losses := [] }

theorem u16780 : Upper (D 7) (R 7) [12,96,18,288,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16780 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16781 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 296 145 96 195 131 387), lower := (rows 13 98 22 296 145 96 64 128 256), losses := [] }

theorem u16781 : Upper (D 7) (R 7) [12,96,18,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16781 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16782 : Route 9 := (fun mask => (mask,id))

def c16782 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16782 : Upper (D 7) (R 7) [12,96,18,288,129,128] 13 := by
  apply FastRouting.sound _ _ [12,96,18,288,129,128] 13 (by decide) (choices 1) [1,2] r16782 c16782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3912
  · exact u3913

def r16783 : Route 9 := (fun mask => (mask,id))

def c16783 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16783 : Upper (D 7) (R 7) [12,96,18,288,192,1] 13 := by
  apply FastRouting.sound _ _ [12,96,18,288,192,1] 13 (by decide) (choices 1) [1,2,128] r16783 c16783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3914
  · exact u3915
  · exact u3916

def b16784 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 38, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 98 22 296 208 34 193 129 385), lower := (rows 13 98 22 296 208 34 64 128 256), losses := [] }

theorem u16784 : Upper (D 7) (R 7) [12,96,18,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16785 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 425, targets := 64 },{ cop := 4, region := 38, targets := 1 }], pairs := [(0,6),(1,0),(2,0),(3,6)], upper := (rows 13 98 22 296 208 160 67 131 259), lower := (rows 13 98 22 296 208 160 64 128 256), losses := [] }

theorem u16785 : Upper (D 7) (R 7) [12,96,18,288,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16786 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 48, targets := 194 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6),(4,7)], upper := (rows 13 98 22 392 49 33 194 194 450), lower := (rows 13 98 22 392 49 33 64 128 256), losses := [] }

theorem u16786 : Upper (D 7) (R 7) [12,96,18,384,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16787 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 22 392 49 34 193 193 449), lower := (rows 13 98 22 392 49 34 64 128 256), losses := [] }

theorem u16787 : Upper (D 7) (R 7) [12,96,18,384,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16788 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 392 49 96 195 131 387), lower := (rows 13 98 22 392 49 96 64 128 256), losses := [] }

theorem u16788 : Upper (D 7) (R 7) [12,96,18,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16789 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 457, targets := 32 },{ cop := 4, region := 70, targets := 128 }], pairs := [(0,5),(1,7),(2,7),(3,5)], upper := (rows 13 98 22 392 49 160 67 195 323), lower := (rows 13 98 22 392 49 160 64 128 256), losses := [] }

theorem u16789 : Upper (D 7) (R 7) [12,96,18,384,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16790 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 102, targets := 128 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 22 392 145 33 98 226 354), lower := (rows 13 98 22 392 145 33 64 128 256), losses := [] }

theorem u16790 : Upper (D 7) (R 7) [12,96,18,384,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16791_1 : Upper (D 7) (R 7) [12,96,18,384,129,2,1] 13 :=
  permutation_upper _ _ _ [12,96,18,384,129,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3917

def r16791 : Route 9 := (fun mask => (mask,id))

def c16791 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16791 : Upper (D 7) (R 7) [12,96,18,384,129,2] 13 := by
  apply FastRouting.sound _ _ [12,96,18,384,129,2] 13 (by decide) (choices 1) [1,32] r16791 c16791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16791_1
  · exact u3918

def b16792 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 392 145 96 99 163 291), lower := (rows 13 98 22 392 145 96 64 128 256), losses := [] }

theorem u16792 : Upper (D 7) (R 7) [12,96,18,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16793 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 457, targets := 32 },{ cop := 0, region := 98, targets := 128 }], pairs := [(0,5),(1,7),(2,7),(3,5)], upper := (rows 13 98 22 392 176 33 67 195 323), lower := (rows 13 98 22 392 176 33 64 128 256), losses := [{ target := 7, region := (rows 1 51 20 8 16 33 97 0 289), good := (rows 367 354 22 264 374 355 64 0 256) }] }

theorem u16793 : Upper (D 7) (R 7) [12,96,18,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16794 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 98 22 392 176 34 65 193 321), lower := (rows 13 98 22 392 176 34 64 128 256), losses := [] }

theorem u16794 : Upper (D 7) (R 7) [12,96,18,384,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16795 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 22 392 176 96 67 131 259), lower := (rows 13 98 22 392 176 96 64 128 256), losses := [] }

theorem u16795 : Upper (D 7) (R 7) [12,96,18,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16796 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 37 88 145 34 450 386 386), lower := (rows 13 98 37 88 145 34 64 128 256), losses := [] }

theorem u16796 : Upper (D 7) (R 7) [12,96,33,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16797 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 4, region := 36, targets := 66 }], pairs := [(1,0),(2,1),(2,6),(3,0)], upper := (rows 13 98 37 88 145 160 322 386 258), lower := (rows 13 98 37 88 145 160 64 128 256), losses := [] }

theorem u16797 : Upper (D 7) (R 7) [12,96,33,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16798 : Route 9 := (fun mask => (mask,id))

def c16798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16798 : Upper (D 7) (R 7) [12,96,33,80,129,256] 13 := by
  apply FastRouting.sound _ _ [12,96,33,80,129,256] 13 (by decide) (choices 1) [2,128] r16798 c16798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3919
  · exact u3920

def b16799 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 408, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 13 98 37 88 146 33 450 386 386), lower := (rows 13 98 37 88 146 33 64 128 256), losses := [] }

theorem u16799 : Upper (D 7) (R 7) [12,96,33,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16799
end Delivery.IrregularNine14.P07
