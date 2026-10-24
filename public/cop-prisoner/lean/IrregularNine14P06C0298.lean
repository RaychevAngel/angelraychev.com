import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0085
import IrregularNine14P06C0086

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17880 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 3, region := 131, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 276 44 82 96 69 133 261), lower := (rows 11 162 276 44 82 96 64 128 256), losses := [] }

theorem u17880 : Upper (D 6) (R 6) [10,160,272,36,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17881 : PairBound 9 := { available := 100, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 73 21 34 100 228 356), lower := (rows 11 162 276 73 21 34 64 128 256), losses := [] }

theorem u17881 : Upper (D 6) (R 6) [10,160,272,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17882 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 73 21 36 98 226 354), lower := (rows 11 162 276 73 21 36 64 128 256), losses := [] }

theorem u17882 : Upper (D 6) (R 6) [10,160,272,65,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17883 : Route 9 := (fun mask => (mask,id))

def c17883 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17883 : Upper (D 6) (R 6) [10,160,272,65,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,272,65,5,64] 13 (by decide) (choices 1) [2,4,32] r17883 c17883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5115
  · exact u5116
  · exact u5117

def b17884 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 73 22 33 100 228 356), lower := (rows 11 162 276 73 22 33 64 128 256), losses := [] }

theorem u17884 : Upper (D 6) (R 6) [10,160,272,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17885 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 73 22 36 97 225 353), lower := (rows 11 162 276 73 22 36 64 128 256), losses := [] }

theorem u17885 : Upper (D 6) (R 6) [10,160,272,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17886 : Route 9 := (fun mask => (mask,id))

def c17886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17886 : Upper (D 6) (R 6) [10,160,272,65,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,272,65,6,64] 13 (by decide) (choices 1) [1,4,32] r17886 c17886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5118
  · exact u5119
  · exact u5120

def b17887 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 276 73 49 34 68 196 324), lower := (rows 11 162 276 73 49 34 64 128 256), losses := [] }

theorem u17887 : Upper (D 6) (R 6) [10,160,272,65,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17888 : Route 9 := (fun mask => (mask,id))

def c17888 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17888 : Upper (D 6) (R 6) [10,160,272,65,33,4] 13 := by
  apply FastRouting.sound _ _ [10,160,272,65,33,4] 13 (by decide) (choices 1) [2,4] r17888 c17888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5121
  · exact u5122

def b17889 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 48, targets := 6 },{ cop := 4, region := 390, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 162 276 73 49 96 70 134 262), lower := (rows 11 162 276 73 49 96 64 128 256), losses := [] }

theorem u17889 : Upper (D 6) (R 6) [10,160,272,65,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17890 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 73 52 33 70 198 326), lower := (rows 11 162 276 73 52 33 64 128 256), losses := [] }

theorem u17890 : Upper (D 6) (R 6) [10,160,272,65,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17891 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 73 52 34 69 197 325), lower := (rows 11 162 276 73 52 34 64 128 256), losses := [] }

theorem u17891 : Upper (D 6) (R 6) [10,160,272,65,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17892 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 276 73 52 36 67 195 323), lower := (rows 11 162 276 73 52 36 64 128 256), losses := [] }

theorem u17892 : Upper (D 6) (R 6) [10,160,272,65,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17893 : Route 9 := (fun mask => (mask,id))

def c17893 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17893 : Upper (D 6) (R 6) [10,160,272,65,36,64] 13 := by
  apply FastRouting.sound _ _ [10,160,272,65,36,64] 13 (by decide) (choices 1) [1,2,4] r17893 c17893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5123
  · exact u5124
  · exact u5125

def b17894 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 73 84 33 102 166 294), lower := (rows 11 162 276 73 84 33 64 128 256), losses := [] }

theorem u17894 : Upper (D 6) (R 6) [10,160,272,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17895 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 73 84 34 101 165 293), lower := (rows 11 162 276 73 84 34 64 128 256), losses := [] }

theorem u17895 : Upper (D 6) (R 6) [10,160,272,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17896 : PairBound 9 := { available := 35, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 73 84 36 99 163 291), lower := (rows 11 162 276 73 84 36 64 128 256), losses := [] }

theorem u17896 : Upper (D 6) (R 6) [10,160,272,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17897 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 73 112 33 70 134 262), lower := (rows 11 162 276 73 112 33 64 128 256), losses := [] }

theorem u17897 : Upper (D 6) (R 6) [10,160,272,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17898 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 73 112 34 69 133 261), lower := (rows 11 162 276 73 112 34 64 128 256), losses := [] }

theorem u17898 : Upper (D 6) (R 6) [10,160,272,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17899 : Route 9 := (fun mask => (mask,id))

def c17899 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17899 : Upper (D 6) (R 6) [10,160,272,65,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,272,65,96,4] 13 (by decide) (choices 1) [1,2,4] r17899 c17899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5126
  · exact u5127
  · exact u5128

def b17900 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 5, region := 194, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 162 276 76 21 33 98 226 354), lower := (rows 11 162 276 76 21 33 64 128 256), losses := [] }

theorem u17900 : Upper (D 6) (R 6) [10,160,272,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17901 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 76 21 34 97 225 353), lower := (rows 11 162 276 76 21 34 64 128 256), losses := [] }

theorem u17901 : Upper (D 6) (R 6) [10,160,272,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17902 : Route 9 := (fun mask => (mask,id))

def c17902 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17902 : Upper (D 6) (R 6) [10,160,272,68,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,5,64] 13 (by decide) (choices 1) [1,2,32] r17902 c17902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5129
  · exact u5130
  · exact u5131

def r17903 : Route 9 := (fun mask => (mask,id))

def c17903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17903 : Upper (D 6) (R 6) [10,160,272,68,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,6,1] 13 (by decide) (choices 1) [1,32] r17903 c17903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5132
  · exact u5133

def r17904 : Route 9 := (fun mask => (mask,id))

def c17904 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17904 : Upper (D 6) (R 6) [10,160,272,68,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,6,64] 13 (by decide) (choices 1) [1,32] r17904 c17904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5134
  · exact u5135

def b17905 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 276 76 49 33 70 198 326), lower := (rows 11 162 276 76 49 33 64 128 256), losses := [] }

theorem u17905 : Upper (D 6) (R 6) [10,160,272,68,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17906 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 276 76 49 34 69 197 325), lower := (rows 11 162 276 76 49 34 64 128 256), losses := [] }

theorem u17906 : Upper (D 6) (R 6) [10,160,272,68,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17907 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 194, targets := 4 }], pairs := [(1,2),(2,5),(4,1)], upper := (rows 11 162 276 76 49 36 67 195 323), lower := (rows 11 162 276 76 49 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 64 128 256), good := (rows 57 160 308 108 49 36 64 128 256) },{ target := 5, region := (rows 1 2 20 24 16 0 65 129 257), good := (rows 459 130 284 76 477 4 64 128 256) }] }

theorem u17907 : Upper (D 6) (R 6) [10,160,272,68,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17908 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 390, targets := 64 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 162 276 76 49 96 71 135 263), lower := (rows 11 162 276 76 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 104 64 128 256), good := (rows 57 160 276 108 49 96 96 128 256) }] }

theorem u17908 : Upper (D 6) (R 6) [10,160,272,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17908 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17909 : Route 9 := (fun mask => (mask,id))

def c17909 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17909 : Upper (D 6) (R 6) [10,160,272,68,36,1] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,36,1] 13 (by decide) (choices 1) [1,2] r17909 c17909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5136
  · exact u5137

def b17910 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 76 52 34 65 193 321), lower := (rows 11 162 276 76 52 34 64 128 256), losses := [] }

theorem u17910 : Upper (D 6) (R 6) [10,160,272,68,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17911 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 3, region := 163, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 11 162 276 76 52 96 67 131 259), lower := (rows 11 162 276 76 52 96 64 128 256), losses := [] }

theorem u17911 : Upper (D 6) (R 6) [10,160,272,68,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17912 : Route 9 := (fun mask => (mask,id))

def c17912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17912 : Upper (D 6) (R 6) [10,160,272,68,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,66,1] 13 (by decide) (choices 1) [1,4,32] r17912 c17912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5138
  · exact u5139
  · exact u5140

def r17913 : Route 9 := (fun mask => (mask,id))

def c17913 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17913 : Upper (D 6) (R 6) [10,160,272,68,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,66,4] 13 (by decide) (choices 1) [1,32] r17913 c17913
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5141
  · exact u5142

def r17914 : Route 9 := (fun mask => (mask,id))

def c17914 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17914 : Upper (D 6) (R 6) [10,160,272,68,96,1] 13 := by
  apply FastRouting.sound _ _ [10,160,272,68,96,1] 13 (by decide) (choices 1) [1,2,4] r17914 c17914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5143
  · exact u5144
  · exact u5145

def b17915 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 276 76 112 34 69 133 261), lower := (rows 11 162 276 76 112 34 64 128 256), losses := [] }

theorem u17915 : Upper (D 6) (R 6) [10,160,272,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17916 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 11 162 276 76 112 36 67 131 259), lower := (rows 11 162 276 76 112 36 64 128 256), losses := [] }

theorem u17916 : Upper (D 6) (R 6) [10,160,272,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17917 : Route 9 := (fun mask => (mask,id))

def c17917 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17917 : Upper (D 6) (R 6) [10,160,272,96,5,1] 13 := by
  apply FastRouting.sound _ _ [10,160,272,96,5,1] 13 (by decide) (choices 1) [2,4] r17917 c17917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5146
  · exact u5147

def b17918 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 276 104 21 34 69 197 325), lower := (rows 11 162 276 104 21 34 64 128 256), losses := [] }

theorem u17918 : Upper (D 6) (R 6) [10,160,272,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17919 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 104 21 36 67 195 323), lower := (rows 11 162 276 104 21 36 64 128 256), losses := [] }

theorem u17919 : Upper (D 6) (R 6) [10,160,272,96,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17920 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 276 104 21 96 71 135 263), lower := (rows 11 162 276 104 21 96 64 128 256), losses := [] }

theorem u17920 : Upper (D 6) (R 6) [10,160,272,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17920 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17921 : Route 9 := (fun mask => (mask,id))

def c17921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17921 : Upper (D 6) (R 6) [10,160,272,96,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,272,96,6,1] 13 (by decide) (choices 1) [1,4] r17921 c17921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5148
  · exact u5149

def b17922 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 104 22 36 65 193 321), lower := (rows 11 162 276 104 22 36 64 128 256), losses := [] }

theorem u17922 : Upper (D 6) (R 6) [10,160,272,96,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17923 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 162 276 104 22 96 69 133 261), lower := (rows 11 162 276 104 22 96 64 128 256), losses := [] }

theorem u17923 : Upper (D 6) (R 6) [10,160,272,96,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17924 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 162 276 104 82 33 69 133 261), lower := (rows 11 162 276 104 82 33 64 128 256), losses := [] }

theorem u17924 : Upper (D 6) (R 6) [10,160,272,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17925 : Route 9 := (fun mask => (mask,id))

def c17925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17925 : Upper (D 6) (R 6) [10,160,272,96,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,272,96,66,4] 13 (by decide) (choices 1) [1,4] r17925 c17925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5150
  · exact u5151

def r17926 : Route 9 := (fun mask => (mask,id))

def c17926 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17926 : Upper (D 6) (R 6) [10,160,272,96,68,1] 13 := by
  apply FastRouting.sound _ _ [10,160,272,96,68,1] 13 (by decide) (choices 1) [1,2,4] r17926 c17926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5152
  · exact u5153
  · exact u5154

def b17927 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 276 104 84 34 69 133 261), lower := (rows 11 162 276 104 84 34 64 128 256), losses := [] }

theorem u17927 : Upper (D 6) (R 6) [10,160,272,96,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17928 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 203, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 276 104 84 36 67 131 259), lower := (rows 11 162 276 104 84 36 64 128 256), losses := [] }

theorem u17928 : Upper (D 6) (R 6) [10,160,272,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17929 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 292 13 81 34 84 212 340), lower := (rows 11 162 292 13 81 34 64 128 256), losses := [] }

theorem u17929 : Upper (D 6) (R 6) [10,160,288,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17930 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 292 13 81 36 82 210 338), lower := (rows 11 162 292 13 81 36 64 128 256), losses := [] }

theorem u17930 : Upper (D 6) (R 6) [10,160,288,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17931 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 292 13 81 48 70 198 326), lower := (rows 11 162 292 13 81 48 64 128 256), losses := [] }

theorem u17931 : Upper (D 6) (R 6) [10,160,288,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17931 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17932 : Route 9 := (fun mask => (mask,id))

def c17932 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17932 : Upper (D 6) (R 6) [10,160,288,5,65,64] 13 := by
  apply FastRouting.sound _ _ [10,160,288,5,65,64] 13 (by decide) (choices 1) [2,4,16] r17932 c17932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5155
  · exact u5156
  · exact u5157

def b17933 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 292 13 82 33 84 212 340), lower := (rows 11 162 292 13 82 33 64 128 256), losses := [] }

theorem u17933 : Upper (D 6) (R 6) [10,160,288,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17934 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 292 13 82 36 81 209 337), lower := (rows 11 162 292 13 82 36 64 128 256), losses := [] }

theorem u17934 : Upper (D 6) (R 6) [10,160,288,5,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17935 : Route 9 := (fun mask => (mask,id))

def c17935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17935 : Upper (D 6) (R 6) [10,160,288,5,66,16] 13 := by
  apply FastRouting.sound _ _ [10,160,288,5,66,16] 13 (by decide) (choices 1) [1,4] r17935 c17935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5158
  · exact u5159

def r17936 : Route 9 := (fun mask => (mask,id))

def c17936 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17936 : Upper (D 6) (R 6) [10,160,288,5,66,64] 13 := by
  apply FastRouting.sound _ _ [10,160,288,5,66,64] 13 (by decide) (choices 1) [1,4,16] r17936 c17936
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5160
  · exact u5161
  · exact u5162

def b17937 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 292 13 84 33 82 210 338), lower := (rows 11 162 292 13 84 33 64 128 256), losses := [] }

theorem u17937 : Upper (D 6) (R 6) [10,160,288,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17938 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 292 13 84 34 81 209 337), lower := (rows 11 162 292 13 84 34 64 128 256), losses := [] }

theorem u17938 : Upper (D 6) (R 6) [10,160,288,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17939 : Route 9 := (fun mask => (mask,id))

def c17939 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17939 : Upper (D 6) (R 6) [10,160,288,5,68,16] 13 := by
  apply FastRouting.sound _ _ [10,160,288,5,68,16] 13 (by decide) (choices 1) [1,2] r17939 c17939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5163
  · exact u5164

#print axioms u17939
end Delivery.IrregularNine14.P06
