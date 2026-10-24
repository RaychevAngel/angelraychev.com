import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0092

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18840 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 134 104 336 33 71 135 263), lower := (rows 25 38 134 104 336 33 64 128 256), losses := [] }

theorem u18840 : Upper (D 6) (R 6) [24,36,130,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18841 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 104 336 34 69 133 261), lower := (rows 25 38 134 104 336 34 64 128 256), losses := [] }

theorem u18841 : Upper (D 6) (R 6) [24,36,130,96,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18842 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 104 336 36 67 131 259), lower := (rows 25 38 134 104 336 36 64 128 256), losses := [] }

theorem u18842 : Upper (D 6) (R 6) [24,36,130,96,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18842 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18843 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 11 112 33 326 390 262), lower := (rows 25 38 196 11 112 33 64 128 256), losses := [] }

theorem u18843 : Upper (D 6) (R 6) [24,36,192,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18844 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 25 38 196 11 112 34 325 389 261), lower := (rows 25 38 196 11 112 34 64 128 256), losses := [] }

theorem u18844 : Upper (D 6) (R 6) [24,36,192,3,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18845 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 11 112 36 323 387 259), lower := (rows 25 38 196 11 112 36 64 128 256), losses := [] }

theorem u18845 : Upper (D 6) (R 6) [24,36,192,3,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18845 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18846 : Route 9 := (fun mask => (mask,id))

def c18846 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18846 : Upper (D 6) (R 6) [24,36,192,3,96,256] 13 := by
  apply FastRouting.sound _ _ [24,36,192,3,96,256] 13 (by decide) (choices 1) [1,2,4] r18846 c18846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5544
  · exact u5545
  · exact u5546

def b18847 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 1, region := 196, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 25 38 196 11 273 34 100 228 356), lower := (rows 25 38 196 11 273 34 64 128 256), losses := [] }

theorem u18847 : Upper (D 6) (R 6) [24,36,192,3,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18848 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 11 273 36 98 226 354), lower := (rows 25 38 196 11 273 36 64 128 256), losses := [] }

theorem u18848 : Upper (D 6) (R 6) [24,36,192,3,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18849 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 196 11 273 96 102 166 294), lower := (rows 25 38 196 11 273 96 64 128 256), losses := [] }

theorem u18849 : Upper (D 6) (R 6) [24,36,192,3,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18850 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 38 196 11 276 33 98 226 354), lower := (rows 25 38 196 11 276 33 64 128 256), losses := [] }

theorem u18850 : Upper (D 6) (R 6) [24,36,192,3,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18851 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 38 196 11 276 34 97 225 353), lower := (rows 25 38 196 11 276 34 64 128 256), losses := [] }

theorem u18851 : Upper (D 6) (R 6) [24,36,192,3,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18852 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 196 11 276 96 99 163 291), lower := (rows 25 38 196 11 276 96 64 128 256), losses := [] }

theorem u18852 : Upper (D 6) (R 6) [24,36,192,3,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18853 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 11 304 33 70 198 326), lower := (rows 25 38 196 11 304 33 64 128 256), losses := [] }

theorem u18853 : Upper (D 6) (R 6) [24,36,192,3,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18854 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 25 38 196 11 304 34 69 197 325), lower := (rows 25 38 196 11 304 34 64 128 256), losses := [] }

theorem u18854 : Upper (D 6) (R 6) [24,36,192,3,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18855 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 11 304 36 67 195 323), lower := (rows 25 38 196 11 304 36 64 128 256), losses := [] }

theorem u18855 : Upper (D 6) (R 6) [24,36,192,3,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18856 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 196 11 304 96 71 135 263), lower := (rows 25 38 196 11 304 96 64 128 256), losses := [] }

theorem u18856 : Upper (D 6) (R 6) [24,36,192,3,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18857 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 11 336 33 102 166 294), lower := (rows 25 38 196 11 336 33 64 128 256), losses := [] }

theorem u18857 : Upper (D 6) (R 6) [24,36,192,3,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18858 : Route 9 := (fun mask => (mask,id))

def c18858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18858 : Upper (D 6) (R 6) [24,36,192,3,320,2] 13 := by
  apply FastRouting.sound _ _ [24,36,192,3,320,2] 13 (by decide) (choices 1) [1,4,32] r18858 c18858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5547
  · exact u5548
  · exact u5549

def b18859 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 11 336 36 99 163 291), lower := (rows 25 38 196 11 336 36 64 128 256), losses := [] }

theorem u18859 : Upper (D 6) (R 6) [24,36,192,3,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18860 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 13 82 33 354 418 290), lower := (rows 25 38 196 13 82 33 64 128 256), losses := [] }

theorem u18860 : Upper (D 6) (R 6) [24,36,192,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18861 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 25 38 196 13 82 34 353 417 289), lower := (rows 25 38 196 13 82 34 64 128 256), losses := [] }

theorem u18861 : Upper (D 6) (R 6) [24,36,192,5,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18862 : Route 9 := (fun mask => (mask,id))

def c18862 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18862 : Upper (D 6) (R 6) [24,36,192,5,66,256] 13 := by
  apply FastRouting.sound _ _ [24,36,192,5,66,256] 13 (by decide) (choices 1) [1,2,32] r18862 c18862
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5550
  · exact u5551
  · exact u5552

def b18863 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 196 13 112 33 322 386 258), lower := (rows 25 38 196 13 112 33 64 128 256), losses := [] }

theorem u18863 : Upper (D 6) (R 6) [24,36,192,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18864 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 25 38 196 13 112 34 323 387 259), lower := (rows 25 38 196 13 112 34 64 128 256), losses := [] }

theorem u18864 : Upper (D 6) (R 6) [24,36,192,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18865 : Route 9 := (fun mask => (mask,id))

def c18865 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18865 : Upper (D 6) (R 6) [24,36,192,5,96,256] 13 := by
  apply FastRouting.sound _ _ [24,36,192,5,96,256] 13 (by decide) (choices 1) [1,2] r18865 c18865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5553
  · exact u5554

def b18866 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 230, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 196 13 273 34 98 226 354), lower := (rows 25 38 196 13 273 34 64 128 256), losses := [] }

theorem u18866 : Upper (D 6) (R 6) [24,36,192,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18867 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 196 13 273 96 98 162 290), lower := (rows 25 38 196 13 273 96 64 128 256), losses := [] }

theorem u18867 : Upper (D 6) (R 6) [24,36,192,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18868 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 13 274 33 98 226 354), lower := (rows 25 38 196 13 274 33 64 128 256), losses := [] }

theorem u18868 : Upper (D 6) (R 6) [24,36,192,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18869 : Route 9 := (fun mask => (mask,id))

def c18869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18869 : Upper (D 6) (R 6) [24,36,192,5,258,2] 13 := by
  apply FastRouting.sound _ _ [24,36,192,5,258,2] 13 (by decide) (choices 1) [1,32] r18869 c18869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5555
  · exact u5556

def b18870 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 196 13 274 96 99 163 291), lower := (rows 25 38 196 13 274 96 64 128 256), losses := [] }

theorem u18870 : Upper (D 6) (R 6) [24,36,192,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18871 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 13 304 33 66 194 322), lower := (rows 25 38 196 13 304 33 64 128 256), losses := [] }

theorem u18871 : Upper (D 6) (R 6) [24,36,192,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18872 : Route 9 := (fun mask => (mask,id))

def c18872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18872 : Upper (D 6) (R 6) [24,36,192,5,288,2] 13 := by
  apply FastRouting.sound _ _ [24,36,192,5,288,2] 13 (by decide) (choices 1) [1,2] r18872 c18872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5557
  · exact u5558

def b18873 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 196 13 304 96 67 131 259), lower := (rows 25 38 196 13 304 96 64 128 256), losses := [] }

theorem u18873 : Upper (D 6) (R 6) [24,36,192,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18874 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 13 336 33 98 162 290), lower := (rows 25 38 196 13 336 33 64 128 256), losses := [] }

theorem u18874 : Upper (D 6) (R 6) [24,36,192,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18875 : Route 9 := (fun mask => (mask,id))

def c18875 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18875 : Upper (D 6) (R 6) [24,36,192,5,320,2] 13 := by
  apply FastRouting.sound _ _ [24,36,192,5,320,2] 13 (by decide) (choices 1) [1,2,32] r18875 c18875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5559
  · exact u5560
  · exact u5561

def b18876 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 38 196 41 82 33 326 390 262), lower := (rows 25 38 196 41 82 33 64 128 256), losses := [] }

theorem u18876 : Upper (D 6) (R 6) [24,36,192,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18877 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 38 196 41 82 34 325 389 261), lower := (rows 25 38 196 41 82 34 64 128 256), losses := [] }

theorem u18877 : Upper (D 6) (R 6) [24,36,192,33,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18878 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 41 82 36 323 387 259), lower := (rows 25 38 196 41 82 36 64 128 256), losses := [] }

theorem u18878 : Upper (D 6) (R 6) [24,36,192,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18879 : Route 9 := (fun mask => (mask,id))

def c18879 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18879 : Upper (D 6) (R 6) [24,36,192,33,66,256] 13 := by
  apply FastRouting.sound _ _ [24,36,192,33,66,256] 13 (by decide) (choices 1) [1,2,4] r18879 c18879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5562
  · exact u5563
  · exact u5564

def b18880 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 38 196 41 274 33 70 198 326), lower := (rows 25 38 196 41 274 33 64 128 256), losses := [] }

theorem u18880 : Upper (D 6) (R 6) [24,36,192,33,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18881 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 25 38 196 41 274 34 69 197 325), lower := (rows 25 38 196 41 274 34 64 128 256), losses := [] }

theorem u18881 : Upper (D 6) (R 6) [24,36,192,33,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18882 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 41 274 36 67 195 323), lower := (rows 25 38 196 41 274 36 64 128 256), losses := [] }

theorem u18882 : Upper (D 6) (R 6) [24,36,192,33,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18883 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 196 41 274 96 71 135 263), lower := (rows 25 38 196 41 274 96 64 128 256), losses := [] }

theorem u18883 : Upper (D 6) (R 6) [24,36,192,33,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18884 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 38 196 41 276 33 66 194 322), lower := (rows 25 38 196 41 276 33 64 128 256), losses := [] }

theorem u18884 : Upper (D 6) (R 6) [24,36,192,33,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18885 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 38 196 41 276 34 67 195 323), lower := (rows 25 38 196 41 276 34 64 128 256), losses := [] }

theorem u18885 : Upper (D 6) (R 6) [24,36,192,33,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18886 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 38 196 41 276 96 67 131 259), lower := (rows 25 38 196 41 276 96 64 128 256), losses := [] }

theorem u18886 : Upper (D 6) (R 6) [24,36,192,33,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18887 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 38 196 41 336 33 70 134 262), lower := (rows 25 38 196 41 336 33 64 128 256), losses := [] }

theorem u18887 : Upper (D 6) (R 6) [24,36,192,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18888 : Route 9 := (fun mask => (mask,id))

def c18888 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18888 : Upper (D 6) (R 6) [24,36,192,33,320,2] 13 := by
  apply FastRouting.sound _ _ [24,36,192,33,320,2] 13 (by decide) (choices 1) [1,2,4] r18888 c18888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5565
  · exact u5566
  · exact u5567

def b18889 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 41 336 36 67 131 259), lower := (rows 25 38 196 41 336 36 64 128 256), losses := [] }

theorem u18889 : Upper (D 6) (R 6) [24,36,192,33,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18890 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 73 274 33 102 166 294), lower := (rows 25 38 196 73 274 33 64 128 256), losses := [] }

theorem u18890 : Upper (D 6) (R 6) [24,36,192,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18891 : Route 9 := (fun mask => (mask,id))

def c18891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18891 : Upper (D 6) (R 6) [24,36,192,65,258,2] 13 := by
  apply FastRouting.sound _ _ [24,36,192,65,258,2] 13 (by decide) (choices 1) [1,4,32] r18891 c18891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5568
  · exact u5569
  · exact u5570

def b18892 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 73 274 36 99 163 291), lower := (rows 25 38 196 73 274 36 64 128 256), losses := [] }

theorem u18892 : Upper (D 6) (R 6) [24,36,192,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18893 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 73 276 33 98 162 290), lower := (rows 25 38 196 73 276 33 64 128 256), losses := [] }

theorem u18893 : Upper (D 6) (R 6) [24,36,192,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18894 : Route 9 := (fun mask => (mask,id))

def c18894 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18894 : Upper (D 6) (R 6) [24,36,192,65,260,2] 13 := by
  apply FastRouting.sound _ _ [24,36,192,65,260,2] 13 (by decide) (choices 1) [1,2,32] r18894 c18894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5571
  · exact u5572
  · exact u5573

def b18895 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 196 73 304 33 70 134 262), lower := (rows 25 38 196 73 304 33 64 128 256), losses := [] }

theorem u18895 : Upper (D 6) (R 6) [24,36,192,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18896 : Route 9 := (fun mask => (mask,id))

def c18896 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18896 : Upper (D 6) (R 6) [24,36,192,65,288,2] 13 := by
  apply FastRouting.sound _ _ [24,36,192,65,288,2] 13 (by decide) (choices 1) [1,2,4] r18896 c18896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5574
  · exact u5575
  · exact u5576

def b18897 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 196 73 304 36 67 131 259), lower := (rows 25 38 196 73 304 36 64 128 256), losses := [] }

theorem u18897 : Upper (D 6) (R 6) [24,36,192,65,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18898 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 206, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 25 38 196 74 273 33 102 166 294), lower := (rows 25 38 196 74 273 33 64 128 256), losses := [] }

theorem u18898 : Upper (D 6) (R 6) [24,36,192,66,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18899 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 42, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 25 38 196 74 273 34 101 165 293), lower := (rows 25 38 196 74 273 34 64 128 256), losses := [] }

theorem u18899 : Upper (D 6) (R 6) [24,36,192,66,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u18899
end Delivery.IrregularNine14.P06
