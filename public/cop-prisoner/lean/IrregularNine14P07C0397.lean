import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0127
import IrregularNine14P07C0128

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23820 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 28 137 400 96 67 131 259), lower := (rows 37 98 28 137 400 96 64 128 256), losses := [] }

theorem u23820 : Upper (D 7) (R 7) [36,96,24,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23821 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 28 138 208 33 323 387 259), lower := (rows 37 98 28 138 208 33 64 128 256), losses := [] }

theorem u23821 : Upper (D 7) (R 7) [36,96,24,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23822 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 46, targets := 1 },{ cop := 0, region := 464, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 37 98 28 138 208 34 321 385 257), lower := (rows 37 98 28 138 208 34 64 128 256), losses := [] }

theorem u23822 : Upper (D 7) (R 7) [36,96,24,130,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23823 : Route 9 := (fun mask => (mask,id))

def c23823 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23823 : Upper (D 7) (R 7) [36,96,24,130,192,256] 13 := by
  apply FastRouting.sound _ _ [36,96,24,130,192,256] 13 (by decide) (choices 1) [1,2] r23823 c23823
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7675
  · exact u7676

def b23824 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 28 138 273 33 194 194 450), lower := (rows 37 98 28 138 273 33 64 128 256), losses := [] }

theorem u23824 : Upper (D 7) (R 7) [36,96,24,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23825 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 37 98 28 138 273 34 193 193 449), lower := (rows 37 98 28 138 273 34 64 128 256), losses := [] }

theorem u23825 : Upper (D 7) (R 7) [36,96,24,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23826 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 28 138 273 96 195 131 387), lower := (rows 37 98 28 138 273 96 64 128 256), losses := [] }

theorem u23826 : Upper (D 7) (R 7) [36,96,24,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23826 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23827 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 28 138 273 160 67 195 323), lower := (rows 37 98 28 138 273 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 61 168 273 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 34 61 170 273 160 0 160 256) }] }

theorem u23827 : Upper (D 7) (R 7) [36,96,24,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23828 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(2,5)], upper := (rows 37 98 28 138 274 33 193 193 449), lower := (rows 37 98 28 138 274 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 30 10 18 0 97 161 289), good := (rows 453 478 28 158 286 449 64 128 256) }] }

theorem u23828 : Upper (D 7) (R 7) [36,96,24,130,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23828 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23829 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 28 138 274 96 193 129 385), lower := (rows 37 98 28 138 274 96 64 128 256), losses := [] }

theorem u23829 : Upper (D 7) (R 7) [36,96,24,130,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23830 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 28 138 274 160 65 193 321), lower := (rows 37 98 28 138 274 160 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 34 61 170 274 160 0 160 256) }] }

theorem u23830 : Upper (D 7) (R 7) [36,96,24,130,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23831 : Route 9 := (fun mask => (mask,id))

def c23831 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23831 : Upper (D 7) (R 7) [36,96,24,130,320,1] 13 := by
  apply FastRouting.sound _ _ [36,96,24,130,320,1] 13 (by decide) (choices 1) [1,2,128] r23831 c23831
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7677
  · exact u7678
  · exact u7679

def b23832 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 37 98 28 138 336 34 193 129 385), lower := (rows 37 98 28 138 336 34 64 128 256), losses := [] }

theorem u23832 : Upper (D 7) (R 7) [36,96,24,130,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23833 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(0,6),(1,7),(4,7)], upper := (rows 37 98 28 138 336 160 67 131 259), lower := (rows 37 98 28 138 336 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 61 168 336 160 64 160 256) },{ target := 6, region := (rows 5 2 4 8 16 168 0 128 256), good := (rows 37 34 61 170 272 160 0 160 256) }] }

theorem u23833 : Upper (D 7) (R 7) [36,96,24,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23834 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 28 138 400 33 67 195 323), lower := (rows 37 98 28 138 400 33 64 128 256), losses := [] }

theorem u23834 : Upper (D 7) (R 7) [36,96,24,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23835 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 37 98 28 138 400 34 65 193 321), lower := (rows 37 98 28 138 400 34 64 128 256), losses := [] }

theorem u23835 : Upper (D 7) (R 7) [36,96,24,130,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23836 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 37 98 28 138 400 96 67 131 259), lower := (rows 37 98 28 138 400 96 64 128 256), losses := [] }

theorem u23836 : Upper (D 7) (R 7) [36,96,24,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23837 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 28 200 273 33 194 130 386), lower := (rows 37 98 28 200 273 33 64 128 256), losses := [] }

theorem u23837 : Upper (D 7) (R 7) [36,96,24,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23838 : Route 9 := (fun mask => (mask,id))

def c23838 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23838 : Upper (D 7) (R 7) [36,96,24,192,257,2] 13 := by
  apply FastRouting.sound _ _ [36,96,24,192,257,2] 13 (by decide) (choices 1) [1,2,128] r23838 c23838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7680
  · exact u7681
  · exact u7682

def b23839 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 98 28 200 273 160 67 131 259), lower := (rows 37 98 28 200 273 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 61 232 273 160 64 160 256) }] }

theorem u23839 : Upper (D 7) (R 7) [36,96,24,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23840 : Route 9 := (fun mask => (mask,id))

def c23840 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23840 : Upper (D 7) (R 7) [36,96,24,192,258,1] 13 := by
  apply FastRouting.sound _ _ [36,96,24,192,258,1] 13 (by decide) (choices 1) [1,2,128] r23840 c23840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7683
  · exact u7684
  · exact u7685

def b23841 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 3, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,5)], upper := (rows 37 98 28 200 274 34 193 129 385), lower := (rows 37 98 28 200 274 34 64 128 256), losses := [] }

theorem u23841 : Upper (D 7) (R 7) [36,96,24,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23842 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 98 28 200 274 160 67 131 259), lower := (rows 37 98 28 200 274 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 61 232 272 160 64 160 256) }] }

theorem u23842 : Upper (D 7) (R 7) [36,96,24,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23843 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 28 200 400 33 67 131 259), lower := (rows 37 98 28 200 400 33 64 128 256), losses := [] }

theorem u23843 : Upper (D 7) (R 7) [36,96,24,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23844 : Route 9 := (fun mask => (mask,id))

def c23844 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23844 : Upper (D 7) (R 7) [36,96,24,192,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,24,192,384,2] 13 (by decide) (choices 1) [1,2] r23844 c23844
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7686
  · exact u7687

def b23845 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(1,0),(4,0)], upper := (rows 37 98 76 25 146 33 450 386 386), lower := (rows 37 98 76 25 146 33 64 128 256), losses := [] }

theorem u23845 : Upper (D 7) (R 7) [36,96,72,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23846 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 3, region := 452, targets := 34 }], pairs := [(0,7),(1,7),(2,1),(2,5)], upper := (rows 37 98 76 25 146 34 449 385 385), lower := (rows 37 98 76 25 146 34 64 128 256), losses := [] }

theorem u23846 : Upper (D 7) (R 7) [36,96,72,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23847 : Route 9 := (fun mask => (mask,id))

def c23847 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23847 : Upper (D 7) (R 7) [36,96,72,17,130,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,17,130,128] 13 (by decide) (choices 1) [1,2,256] r23847 c23847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7688
  · exact u7689
  · exact u7690

def r23848 : Route 9 := (fun mask => (mask,id))

def c23848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23848 : Upper (D 7) (R 7) [36,96,72,17,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,72,17,130,256] 13 (by decide) (choices 1) [1,2,128] r23848 c23848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7691
  · exact u7692
  · exact u7693

def b23849 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(1,0),(4,0)], upper := (rows 37 98 76 25 274 33 194 130 386), lower := (rows 37 98 76 25 274 33 64 128 256), losses := [] }

theorem u23849 : Upper (D 7) (R 7) [36,96,72,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23849 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23850 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 35, targets := 128 },{ cop := 3, region := 196, targets := 34 }], pairs := [(0,7),(1,7),(2,1),(2,5)], upper := (rows 37 98 76 25 274 34 193 129 385), lower := (rows 37 98 76 25 274 34 64 128 256), losses := [] }

theorem u23850 : Upper (D 7) (R 7) [36,96,72,17,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23851 : Route 9 := (fun mask => (mask,id))

def c23851 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23851 : Upper (D 7) (R 7) [36,96,72,17,258,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,17,258,128] 13 (by decide) (choices 1) [1,2,128] r23851 c23851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7694
  · exact u7695
  · exact u7696

def b23852 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(1,0),(4,0)], upper := (rows 37 98 76 25 400 33 194 130 386), lower := (rows 37 98 76 25 400 33 64 128 256), losses := [] }

theorem u23852 : Upper (D 7) (R 7) [36,96,72,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23853 : Route 9 := (fun mask => (mask,id))

def c23853 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23853 : Upper (D 7) (R 7) [36,96,72,17,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,17,384,2] 13 (by decide) (choices 1) [1,2,128] r23853 c23853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7697
  · exact u7698
  · exact u7699

def r23854 : Route 9 := (fun mask => (mask,id))

def c23854 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23854 : Upper (D 7) (R 7) [36,96,72,17,384,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,17,384,128] 13 (by decide) (choices 1) [1,2] r23854 c23854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7700
  · exact u7701

def b23855 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 26 145 33 450 386 386), lower := (rows 37 98 76 26 145 33 64 128 256), losses := [] }

theorem u23855 : Upper (D 7) (R 7) [36,96,72,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23855 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23856 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 37 98 76 26 145 34 449 385 385), lower := (rows 37 98 76 26 145 34 64 128 256), losses := [] }

theorem u23856 : Upper (D 7) (R 7) [36,96,72,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23856 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23857 : Route 9 := (fun mask => (mask,id))

def c23857 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23857 : Upper (D 7) (R 7) [36,96,72,18,129,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,18,129,128] 13 (by decide) (choices 1) [1,2,256] r23857 c23857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7702
  · exact u7703
  · exact u7704

def r23858 : Route 9 := (fun mask => (mask,id))

def c23858 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23858 : Upper (D 7) (R 7) [36,96,72,18,129,256] 13 := by
  apply FastRouting.sound _ _ [36,96,72,18,129,256] 13 (by decide) (choices 1) [1,2,128] r23858 c23858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7705
  · exact u7706
  · exact u7707

def b23859 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 26 273 33 194 130 386), lower := (rows 37 98 76 26 273 33 64 128 256), losses := [] }

theorem u23859 : Upper (D 7) (R 7) [36,96,72,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23859 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23860 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 37 98 76 26 273 34 193 129 385), lower := (rows 37 98 76 26 273 34 64 128 256), losses := [] }

theorem u23860 : Upper (D 7) (R 7) [36,96,72,18,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23861 : Route 9 := (fun mask => (mask,id))

def c23861 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23861 : Upper (D 7) (R 7) [36,96,72,18,257,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,18,257,128] 13 (by decide) (choices 1) [1,2,128] r23861 c23861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7708
  · exact u7709
  · exact u7710

def b23862 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 76 26 400 33 195 131 387), lower := (rows 37 98 76 26 400 33 64 128 256), losses := [] }

theorem u23862 : Upper (D 7) (R 7) [36,96,72,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23863 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 37 98 76 26 400 34 193 129 385), lower := (rows 37 98 76 26 400 34 64 128 256), losses := [] }

theorem u23863 : Upper (D 7) (R 7) [36,96,72,18,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23864 : Route 9 := (fun mask => (mask,id))

def c23864 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23864 : Upper (D 7) (R 7) [36,96,72,18,384,128] 13 := by
  apply FastRouting.sound _ _ [36,96,72,18,384,128] 13 (by decide) (choices 1) [1,2] r23864 c23864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7711
  · exact u7712

def b23865 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(1,0),(4,0)], upper := (rows 37 98 76 137 146 33 338 402 274), lower := (rows 37 98 76 137 146 33 64 128 256), losses := [] }

theorem u23865 : Upper (D 7) (R 7) [36,96,72,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23866 : Route 9 := (fun mask => (mask,id))

def c23866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23866 : Upper (D 7) (R 7) [36,96,72,129,130,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,130,2] 13 (by decide) (choices 1) [1,16,256] r23866 c23866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7713
  · exact u7714
  · exact u7715

def r23867 : Route 9 := (fun mask => (mask,id))

def c23867 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23867 : Upper (D 7) (R 7) [36,96,72,129,130,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,130,16] 13 (by decide) (choices 1) [1,2,256] r23867 c23867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7716
  · exact u7717
  · exact u7718

def r23868 : Route 9 := (fun mask => (mask,id))

def c23868 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23868 : Upper (D 7) (R 7) [36,96,72,129,130,256] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,130,256] 13 (by decide) (choices 1) [1,2,16] r23868 c23868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7719
  · exact u7720
  · exact u7721

def r23869 : Route 9 := (fun mask => (mask,id))

def c23869 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23869 : Upper (D 7) (R 7) [36,96,72,129,257,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,257,2] 13 (by decide) (choices 1) [2,16,128] r23869 c23869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7722
  · exact u7723
  · exact u7724

def r23870 : Route 9 := (fun mask => (mask,id))

def c23870 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23870 : Upper (D 7) (R 7) [36,96,72,129,257,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,257,16] 13 (by decide) (choices 1) [2,128] r23870 c23870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7725
  · exact u7726

def b23871 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 338, targets := 128 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 98 76 137 273 160 82 146 274), lower := (rows 37 98 76 137 273 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 109 169 273 160 64 160 256) }] }

theorem u23871 : Upper (D 7) (R 7) [36,96,72,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23872 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(1,0),(4,0)], upper := (rows 37 98 76 137 274 33 210 146 402), lower := (rows 37 98 76 137 274 33 64 128 256), losses := [] }

theorem u23872 : Upper (D 7) (R 7) [36,96,72,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23873 : Route 9 := (fun mask => (mask,id))

def c23873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23873 : Upper (D 7) (R 7) [36,96,72,129,258,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,258,2] 13 (by decide) (choices 1) [1,16,128] r23873 c23873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7727
  · exact u7728
  · exact u7729

def r23874 : Route 9 := (fun mask => (mask,id))

def c23874 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23874 : Upper (D 7) (R 7) [36,96,72,129,258,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,258,16] 13 (by decide) (choices 1) [1,2,128] r23874 c23874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7730
  · exact u7731
  · exact u7732

def b23875 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 37 98 76 137 274 160 83 147 275), lower := (rows 37 98 76 137 274 160 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 168 64 128 256), good := (rows 38 98 110 168 274 160 64 160 256) },{ target := 1, region := (rows 5 0 4 8 16 168 64 128 256), good := (rows 37 96 109 169 272 160 64 160 256) }] }

theorem u23875 : Upper (D 7) (R 7) [36,96,72,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23876 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 466, targets := 1 },{ cop := 2, region := 33, targets := 66 }], pairs := [(0,1),(0,6),(1,0),(4,0)], upper := (rows 37 98 76 137 400 33 82 146 274), lower := (rows 37 98 76 137 400 33 64 128 256), losses := [] }

theorem u23876 : Upper (D 7) (R 7) [36,96,72,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23877 : Route 9 := (fun mask => (mask,id))

def c23877 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23877 : Upper (D 7) (R 7) [36,96,72,129,384,2] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,384,2] 13 (by decide) (choices 1) [1,2,16] r23877 c23877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7733
  · exact u7734
  · exact u7735

def r23878 : Route 9 := (fun mask => (mask,id))

def c23878 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23878 : Upper (D 7) (R 7) [36,96,72,129,384,16] 13 := by
  apply FastRouting.sound _ _ [36,96,72,129,384,16] 13 (by decide) (choices 1) [1,2] r23878 c23878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7736
  · exact u7737

def b23879 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 76 138 19 33 464 400 400), lower := (rows 37 98 76 138 19 33 64 128 256), losses := [] }

theorem u23879 : Upper (D 7) (R 7) [36,96,72,130,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u23879
end Delivery.IrregularNine14.P07
