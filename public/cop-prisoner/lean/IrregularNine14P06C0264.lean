import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0063
import IrregularNine14P06C0064

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b15840 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 88 21 34 100 228 356), lower := (rows 11 131 292 88 21 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 55 24 16 35 119 183 311), good := (rows 494 486 484 476 508 486 64 128 256) }] }

theorem u15840 : Upper (D 6) (R 6) [10,129,288,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15841 : PairBound 9 := { available := 98, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 88 21 36 98 226 354), lower := (rows 11 131 292 88 21 36 64 128 256), losses := [] }

theorem u15841 : Upper (D 6) (R 6) [10,129,288,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15842 : Route 9 := (fun mask => (mask,id))

def c15842 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15842 : Upper (D 6) (R 6) [10,129,288,80,5,64] 13 := by
  apply FastRouting.sound _ _ [10,129,288,80,5,64] 13 (by decide) (choices 1) [2,4,32] r15842 c15842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3836
  · exact u3837
  · exact u3838

def b15843 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 324, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 88 22 33 100 228 356), lower := (rows 11 131 292 88 22 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 24 16 32 100 164 292), good := (rows 10 130 484 88 478 484 64 128 256) }] }

theorem u15843 : Upper (D 6) (R 6) [10,129,288,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15843 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15844 : PairBound 9 := { available := 97, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 88 22 36 97 225 353), lower := (rows 11 131 292 88 22 36 64 128 256), losses := [] }

theorem u15844 : Upper (D 6) (R 6) [10,129,288,80,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15844 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15845 : Route 9 := (fun mask => (mask,id))

def c15845 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15845 : Upper (D 6) (R 6) [10,129,288,80,6,64] 13 := by
  apply FastRouting.sound _ _ [10,129,288,80,6,64] 13 (by decide) (choices 1) [1,4,32] r15845 c15845
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3839
  · exact u3840
  · exact u3841

def b15846 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 88 49 34 68 196 324), lower := (rows 11 131 292 88 49 34 64 128 256), losses := [] }

theorem u15846 : Upper (D 6) (R 6) [10,129,288,80,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15847 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 88 49 36 70 198 326), lower := (rows 11 131 292 88 49 36 64 128 256), losses := [] }

theorem u15847 : Upper (D 6) (R 6) [10,129,288,80,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15848 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 390, targets := 64 },{ cop := 0, region := 356, targets := 1 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 131 292 88 49 96 70 134 262), lower := (rows 11 131 292 88 49 96 64 128 256), losses := [] }

theorem u15848 : Upper (D 6) (R 6) [10,129,288,80,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15848 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15849 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 332, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 131 292 88 50 33 68 196 324), lower := (rows 11 131 292 88 50 33 64 128 256), losses := [] }

theorem u15849 : Upper (D 6) (R 6) [10,129,288,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15850 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 88 50 36 69 197 325), lower := (rows 11 131 292 88 50 36 64 128 256), losses := [] }

theorem u15850 : Upper (D 6) (R 6) [10,129,288,80,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15851 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 11 131 292 88 50 96 69 133 261), lower := (rows 11 131 292 88 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 104 64 128 256), good := (rows 58 146 292 120 50 96 96 128 256) },{ target := 1, region := (rows 1 0 23 24 16 123 67 131 259), good := (rows 493 485 292 124 508 96 96 128 256) }] }

theorem u15851 : Upper (D 6) (R 6) [10,129,288,80,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15851 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15852 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5),(2,0),(3,0)], upper := (rows 11 131 292 104 21 34 84 212 340), lower := (rows 11 131 292 104 21 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 42 162 292 104 508 34 64 128 256) }] }

theorem u15852 : Upper (D 6) (R 6) [10,129,288,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15853 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 104 21 36 82 210 338), lower := (rows 11 131 292 104 21 36 64 128 256), losses := [] }

theorem u15853 : Upper (D 6) (R 6) [10,129,288,96,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15854 : Route 9 := (fun mask => (mask,id))

def c15854 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15854 : Upper (D 6) (R 6) [10,129,288,96,5,16] 13 := by
  apply FastRouting.sound _ _ [10,129,288,96,5,16] 13 (by decide) (choices 1) [2,4] r15854 c15854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3842
  · exact u3843

def b15855 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 292 104 21 96 86 150 278), lower := (rows 11 131 292 104 21 96 64 128 256), losses := [] }

theorem u15855 : Upper (D 6) (R 6) [10,129,288,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15856 : PairBound 9 := { available := 84, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 131 292 104 22 33 84 212 340), lower := (rows 11 131 292 104 22 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 17 32 113 177 305), good := (rows 478 466 492 492 478 508 64 128 256) }] }

theorem u15856 : Upper (D 6) (R 6) [10,129,288,96,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15857 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 104 22 36 81 209 337), lower := (rows 11 131 292 104 22 36 64 128 256), losses := [] }

theorem u15857 : Upper (D 6) (R 6) [10,129,288,96,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15857 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15858 : Route 9 := (fun mask => (mask,id))

def c15858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15858 : Upper (D 6) (R 6) [10,129,288,96,6,16] 13 := by
  apply FastRouting.sound _ _ [10,129,288,96,6,16] 13 (by decide) (choices 1) [1,4] r15858 c15858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3844
  · exact u3845

def b15859 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 292 104 22 96 85 149 277), lower := (rows 11 131 292 104 22 96 64 128 256), losses := [] }

theorem u15859 : Upper (D 6) (R 6) [10,129,288,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15859 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15860 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 131 292 104 81 34 84 148 276), lower := (rows 11 131 292 104 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 42 162 292 104 508 34 64 128 256) }] }

theorem u15860 : Upper (D 6) (R 6) [10,129,288,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15861 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 104 81 36 86 150 278), lower := (rows 11 131 292 104 81 36 64 128 256), losses := [] }

theorem u15861 : Upper (D 6) (R 6) [10,129,288,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15862 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 292 104 81 48 70 134 262), lower := (rows 11 131 292 104 81 48 64 128 256), losses := [] }

theorem u15862 : Upper (D 6) (R 6) [10,129,288,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15862 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15863 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 11 131 292 104 82 33 84 148 276), lower := (rows 11 131 292 104 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 19 32 97 161 289), good := (rows 478 466 492 492 82 508 64 128 256) }] }

theorem u15863 : Upper (D 6) (R 6) [10,129,288,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15864 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 104 82 36 85 149 277), lower := (rows 11 131 292 104 82 36 64 128 256), losses := [] }

theorem u15864 : Upper (D 6) (R 6) [10,129,288,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15865 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 292 104 82 48 69 133 261), lower := (rows 11 131 292 104 82 48 64 128 256), losses := [] }

theorem u15865 : Upper (D 6) (R 6) [10,129,288,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15865 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15866 : Route 9 := (fun mask => (mask,id))

def c15866 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15866 : Upper (D 6) (R 6) [10,129,288,96,68,1] 13 := by
  apply FastRouting.sound _ _ [10,129,288,96,68,1] 13 (by decide) (choices 1) [2,4,16] r15866 c15866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3846
  · exact u3847
  · exact u3848

def r15867 : Route 9 := (fun mask => (mask,id))

def c15867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15867 : Upper (D 6) (R 6) [10,129,288,96,68,2] 13 := by
  apply FastRouting.sound _ _ [10,129,288,96,68,2] 13 (by decide) (choices 1) [1,4,16] r15867 c15867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3849
  · exact u3850
  · exact u3851

def b15868 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 131 292 104 84 36 83 147 275), lower := (rows 11 131 292 104 84 36 64 128 256), losses := [] }

theorem u15868 : Upper (D 6) (R 6) [10,129,288,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15869 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 292 104 84 48 71 135 263), lower := (rows 11 131 292 104 84 48 64 128 256), losses := [] }

theorem u15869 : Upper (D 6) (R 6) [10,129,288,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15869 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15870 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 344, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 134 37 25 84 34 352 480 352), lower := (rows 11 134 37 25 84 34 64 128 256), losses := [] }

theorem u15870 : Upper (D 6) (R 6) [10,132,33,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15871 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 134 37 25 84 96 354 418 290), lower := (rows 11 134 37 25 84 96 64 128 256), losses := [] }

theorem u15871 : Upper (D 6) (R 6) [10,132,33,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15872 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 134 37 25 84 288 98 226 354), lower := (rows 11 134 37 25 84 288 64 128 256), losses := [] }

theorem u15872 : Upper (D 6) (R 6) [10,132,33,17,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15872 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15873 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 344, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 134 37 25 276 34 96 224 352), lower := (rows 11 134 37 25 276 34 64 128 256), losses := [] }

theorem u15873 : Upper (D 6) (R 6) [10,132,33,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15874 : Route 9 := (fun mask => (mask,id))

def c15874 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15874 : Upper (D 6) (R 6) [10,132,33,17,260,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,17,260,64] 13 (by decide) (choices 1) [2,32] r15874 c15874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3852
  · exact u3853

def b15875 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 344, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 134 37 25 336 34 100 228 356), lower := (rows 11 134 37 25 336 34 64 128 256), losses := [] }

theorem u15875 : Upper (D 6) (R 6) [10,132,33,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15876 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 134 37 25 336 36 98 226 354), lower := (rows 11 134 37 25 336 36 64 128 256), losses := [] }

theorem u15876 : Upper (D 6) (R 6) [10,132,33,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15877 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 134 37 25 336 96 102 166 294), lower := (rows 11 134 37 25 336 96 64 128 256), losses := [] }

theorem u15877 : Upper (D 6) (R 6) [10,132,33,17,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15878 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 134 37 28 81 34 352 480 352), lower := (rows 11 134 37 28 81 34 64 128 256), losses := [] }

theorem u15878 : Upper (D 6) (R 6) [10,132,33,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15879 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 44, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 134 37 28 81 96 354 418 290), lower := (rows 11 134 37 28 81 96 64 128 256), losses := [] }

theorem u15879 : Upper (D 6) (R 6) [10,132,33,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15880 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(4,2)], upper := (rows 11 134 37 28 81 288 98 226 354), lower := (rows 11 134 37 28 81 288 64 128 256), losses := [] }

theorem u15880 : Upper (D 6) (R 6) [10,132,33,20,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15880 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15881 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 28 82 33 352 480 352), lower := (rows 11 134 37 28 82 33 64 128 256), losses := [] }

theorem u15881 : Upper (D 6) (R 6) [10,132,33,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15882 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 0, region := 368, targets := 4 },{ cop := 2, region := 386, targets := 64 }], pairs := [(1,6),(2,1),(4,2)], upper := (rows 11 134 37 28 82 96 353 417 289), lower := (rows 11 134 37 28 82 96 64 128 256), losses := [] }

theorem u15882 : Upper (D 6) (R 6) [10,132,33,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15883 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 356, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(4,2)], upper := (rows 11 134 37 28 82 288 97 225 353), lower := (rows 11 134 37 28 82 288 64 128 256), losses := [] }

theorem u15883 : Upper (D 6) (R 6) [10,132,33,20,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15883 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15884 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 134 37 28 273 34 96 224 352), lower := (rows 11 134 37 28 273 34 64 128 256), losses := [] }

theorem u15884 : Upper (D 6) (R 6) [10,132,33,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15885 : Route 9 := (fun mask => (mask,id))

def c15885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15885 : Upper (D 6) (R 6) [10,132,33,20,257,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,20,257,64] 13 (by decide) (choices 1) [2,32] r15885 c15885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3854
  · exact u3855

def b15886 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 28 274 33 96 224 352), lower := (rows 11 134 37 28 274 33 64 128 256), losses := [] }

theorem u15886 : Upper (D 6) (R 6) [10,132,33,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15887 : Route 9 := (fun mask => (mask,id))

def c15887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15887 : Upper (D 6) (R 6) [10,132,33,20,258,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,20,258,64] 13 (by decide) (choices 1) [1,32] r15887 c15887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3856
  · exact u3857

def b15888 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 28 336 33 98 226 354), lower := (rows 11 134 37 28 336 33 64 128 256), losses := [] }

theorem u15888 : Upper (D 6) (R 6) [10,132,33,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15889 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(4,1),(4,2)], upper := (rows 11 134 37 28 336 34 97 225 353), lower := (rows 11 134 37 28 336 34 64 128 256), losses := [] }

theorem u15889 : Upper (D 6) (R 6) [10,132,33,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15890 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 2, region := 130, targets := 64 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 134 37 28 336 96 99 163 291), lower := (rows 11 134 37 28 336 96 64 128 256), losses := [{ target := 6, region := (rows 9 14 4 8 16 32 0 132 260), good := (rows 11 390 423 415 272 32 0 128 256) }] }

theorem u15890 : Upper (D 6) (R 6) [10,132,33,20,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15891 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 56 336 33 70 198 326), lower := (rows 11 134 37 56 336 33 64 128 256), losses := [] }

theorem u15891 : Upper (D 6) (R 6) [10,132,33,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15892 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 134 37 56 336 34 69 197 325), lower := (rows 11 134 37 56 336 34 64 128 256), losses := [] }

theorem u15892 : Upper (D 6) (R 6) [10,132,33,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15893 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 134 37 56 336 36 67 195 323), lower := (rows 11 134 37 56 336 36 64 128 256), losses := [] }

theorem u15893 : Upper (D 6) (R 6) [10,132,33,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15894 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 37 56 336 96 71 135 263), lower := (rows 11 134 37 56 336 96 64 128 256), losses := [] }

theorem u15894 : Upper (D 6) (R 6) [10,132,33,48,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15895 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 37 73 50 36 336 464 336), lower := (rows 11 134 37 73 50 36 64 128 256), losses := [] }

theorem u15895 : Upper (D 6) (R 6) [10,132,33,65,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15896 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 37 73 50 48 324 452 324), lower := (rows 11 134 37 73 50 48 64 128 256), losses := [] }

theorem u15896 : Upper (D 6) (R 6) [10,132,33,65,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15896 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15897 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 402, targets := 1 },{ cop := 2, region := 402, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 134 37 73 50 96 340 404 276), lower := (rows 11 134 37 73 50 96 64 128 256), losses := [] }

theorem u15897 : Upper (D 6) (R 6) [10,132,33,65,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15898 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 134 37 73 50 288 84 212 340), lower := (rows 11 134 37 73 50 288 64 128 256), losses := [] }

theorem u15898 : Upper (D 6) (R 6) [10,132,33,65,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15898 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15899 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 2, region := 344, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 134 37 73 112 34 340 404 276), lower := (rows 11 134 37 73 112 34 64 128 256), losses := [] }

theorem u15899 : Upper (D 6) (R 6) [10,132,33,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u15899
end Delivery.IrregularNine14.P06
