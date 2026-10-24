import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0086
import IrregularNine14P06C0087

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17940 : Route 9 := (fun mask => (mask,id))

def c17940 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17940 : Upper (D 6) (R 6) [10,160,288,5,68,64] 13 := by
  apply FastRouting.sound _ _ [10,160,288,5,68,64] 13 (by decide) (choices 1) [1,2,16] r17940 c17940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5165
  · exact u5166
  · exact u5167

def b17941 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 292 25 84 33 70 198 326), lower := (rows 11 162 292 25 84 33 64 128 256), losses := [] }

theorem u17941 : Upper (D 6) (R 6) [10,160,288,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17942 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 292 25 84 34 69 197 325), lower := (rows 11 162 292 25 84 34 64 128 256), losses := [] }

theorem u17942 : Upper (D 6) (R 6) [10,160,288,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17943 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 292 25 84 36 67 195 323), lower := (rows 11 162 292 25 84 36 64 128 256), losses := [] }

theorem u17943 : Upper (D 6) (R 6) [10,160,288,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17944 : Route 9 := (fun mask => (mask,id))

def c17944 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17944 : Upper (D 6) (R 6) [10,160,288,17,68,64] 13 := by
  apply FastRouting.sound _ _ [10,160,288,17,68,64] 13 (by decide) (choices 1) [1,2,4] r17944 c17944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5168
  · exact u5169
  · exact u5170

def r17945 : Route 9 := (fun mask => (mask,id))

def c17945 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17945 : Upper (D 6) (R 6) [10,160,288,20,65,1] 13 := by
  apply FastRouting.sound _ _ [10,160,288,20,65,1] 13 (by decide) (choices 1) [2,4] r17945 c17945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5171
  · exact u5172

def b17946 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 292 28 81 34 69 197 325), lower := (rows 11 162 292 28 81 34 64 128 256), losses := [] }

theorem u17946 : Upper (D 6) (R 6) [10,160,288,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17947 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 292 28 81 36 67 195 323), lower := (rows 11 162 292 28 81 36 64 128 256), losses := [] }

theorem u17947 : Upper (D 6) (R 6) [10,160,288,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17948 : Route 9 := (fun mask => (mask,id))

def c17948 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17948 : Upper (D 6) (R 6) [10,160,288,20,65,64] 13 := by
  apply FastRouting.sound _ _ [10,160,288,20,65,64] 13 (by decide) (choices 1) [1,2,4] r17948 c17948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5173
  · exact u5174
  · exact u5175

def r17949 : Route 9 := (fun mask => (mask,id))

def c17949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17949 : Upper (D 6) (R 6) [10,160,288,20,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,288,20,66,1] 13 (by decide) (choices 1) [1,4] r17949 c17949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5176
  · exact u5177

def b17950 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 292 28 82 36 65 193 321), lower := (rows 11 162 292 28 82 36 64 128 256), losses := [] }

theorem u17950 : Upper (D 6) (R 6) [10,160,288,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17951 : Route 9 := (fun mask => (mask,id))

def c17951 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17951 : Upper (D 6) (R 6) [10,160,288,20,66,64] 13 := by
  apply FastRouting.sound _ _ [10,160,288,20,66,64] 13 (by decide) (choices 1) [1,4] r17951 c17951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5178
  · exact u5179

def b17952 : PairBound 9 := { available := 84, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 292 73 21 34 84 212 340), lower := (rows 11 162 292 73 21 34 64 128 256), losses := [] }

theorem u17952 : Upper (D 6) (R 6) [10,160,288,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17953 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 292 73 21 36 82 210 338), lower := (rows 11 162 292 73 21 36 64 128 256), losses := [] }

theorem u17953 : Upper (D 6) (R 6) [10,160,288,65,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17954 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 486, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 292 73 21 48 70 198 326), lower := (rows 11 162 292 73 21 48 64 128 256), losses := [] }

theorem u17954 : Upper (D 6) (R 6) [10,160,288,65,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17954 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17955 : Route 9 := (fun mask => (mask,id))

def c17955 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17955 : Upper (D 6) (R 6) [10,160,288,65,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,288,65,5,64] 13 (by decide) (choices 1) [2,4,16] r17955 c17955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5180
  · exact u5181
  · exact u5182

def b17956 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 292 73 22 33 84 212 340), lower := (rows 11 162 292 73 22 33 64 128 256), losses := [] }

theorem u17956 : Upper (D 6) (R 6) [10,160,288,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17957 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 292 73 22 36 81 209 337), lower := (rows 11 162 292 73 22 36 64 128 256), losses := [] }

theorem u17957 : Upper (D 6) (R 6) [10,160,288,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17958 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 292 73 22 48 69 197 325), lower := (rows 11 162 292 73 22 48 64 128 256), losses := [] }

theorem u17958 : Upper (D 6) (R 6) [10,160,288,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17958 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17959 : Route 9 := (fun mask => (mask,id))

def c17959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17959 : Upper (D 6) (R 6) [10,160,288,65,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,288,65,6,64] 13 (by decide) (choices 1) [1,4,16] r17959 c17959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5183
  · exact u5184
  · exact u5185

def b17960 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 292 73 84 33 86 150 278), lower := (rows 11 162 292 73 84 33 64 128 256), losses := [] }

theorem u17960 : Upper (D 6) (R 6) [10,160,288,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17961 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 292 73 84 34 85 149 277), lower := (rows 11 162 292 73 84 34 64 128 256), losses := [] }

theorem u17961 : Upper (D 6) (R 6) [10,160,288,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17962 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 292 73 84 36 83 147 275), lower := (rows 11 162 292 73 84 36 64 128 256), losses := [] }

theorem u17962 : Upper (D 6) (R 6) [10,160,288,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17963 : Route 9 := (fun mask => (mask,id))

def c17963 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17963 : Upper (D 6) (R 6) [10,160,288,65,68,16] 13 := by
  apply FastRouting.sound _ _ [10,160,288,65,68,16] 13 (by decide) (choices 1) [1,2,4] r17963 c17963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5186
  · exact u5187
  · exact u5188

def r17964 : Route 9 := (fun mask => (mask,id))

def c17964 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17964 : Upper (D 6) (R 6) [10,160,288,68,5,1] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68,5,1] 13 (by decide) (choices 1) [2,16] r17964 c17964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5189
  · exact u5190

def b17965 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 292 76 21 34 81 209 337), lower := (rows 11 162 292 76 21 34 64 128 256), losses := [] }

theorem u17965 : Upper (D 6) (R 6) [10,160,288,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17966 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 226, targets := 4 }], pairs := [(1,2),(3,5)], upper := (rows 11 162 292 76 21 48 67 195 323), lower := (rows 11 162 292 76 21 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 65 129 257), good := (rows 459 130 260 76 477 24 64 128 256) }] }

theorem u17966 : Upper (D 6) (R 6) [10,160,288,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17966 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17967 : Route 9 := (fun mask => (mask,id))

def c17967 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17967 : Upper (D 6) (R 6) [10,160,288,68,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68,5,64] 13 (by decide) (choices 1) [1,2,16] r17967 c17967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5191
  · exact u5192
  · exact u5193

def r17968 : Route 9 := (fun mask => (mask,id))

def c17968 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17968 : Upper (D 6) (R 6) [10,160,288,68,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68,6,1] 13 (by decide) (choices 1) [1,16] r17968 c17968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5194
  · exact u5195

def b17969 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 162 292 76 22 48 65 193 321), lower := (rows 11 162 292 76 22 48 64 128 256), losses := [] }

theorem u17969 : Upper (D 6) (R 6) [10,160,288,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17969 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17970 : Route 9 := (fun mask => (mask,id))

def c17970 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17970 : Upper (D 6) (R 6) [10,160,288,68,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68,6,64] 13 (by decide) (choices 1) [1,16] r17970 c17970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5196
  · exact u5197

def r17971 : Route 9 := (fun mask => (mask,id))

def c17971 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17971 : Upper (D 6) (R 6) [10,160,288,68,65,1] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68,65,1] 13 (by decide) (choices 1) [2,4,16] r17971 c17971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5198
  · exact u5199
  · exact u5200

def b17972 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 292 76 81 34 85 149 277), lower := (rows 11 162 292 76 81 34 64 128 256), losses := [] }

theorem u17972 : Upper (D 6) (R 6) [10,160,288,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17973 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 292 76 81 36 83 147 275), lower := (rows 11 162 292 76 81 36 64 128 256), losses := [] }

theorem u17973 : Upper (D 6) (R 6) [10,160,288,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17974 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 162 292 76 81 48 71 135 263), lower := (rows 11 162 292 76 81 48 64 128 256), losses := [] }

theorem u17974 : Upper (D 6) (R 6) [10,160,288,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17974 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17975 : Route 9 := (fun mask => (mask,id))

def c17975 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17975 : Upper (D 6) (R 6) [10,160,288,68,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68,66,1] 13 (by decide) (choices 1) [1,4,16] r17975 c17975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5201
  · exact u5202
  · exact u5203

def b17976 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 292 76 82 36 81 145 273), lower := (rows 11 162 292 76 82 36 64 128 256), losses := [] }

theorem u17976 : Upper (D 6) (R 6) [10,160,288,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17977 : Route 9 := (fun mask => (mask,id))

def c17977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17977 : Upper (D 6) (R 6) [10,160,288,68,66,16] 13 := by
  apply FastRouting.sound _ _ [10,160,288,68,66,16] 13 (by decide) (choices 1) [1,4] r17977 c17977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5204
  · exact u5205

def b17978 : PairBound 9 := { available := 70, camps := [{ cop := 5, region := 454, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 292 88 21 33 70 198 326), lower := (rows 11 162 292 88 21 33 64 128 256), losses := [{ target := 0, region := (rows 0 38 38 24 16 32 119 183 311), good := (rows 462 486 486 472 478 486 64 128 256) }] }

theorem u17978 : Upper (D 6) (R 6) [10,160,288,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17979 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 292 88 21 34 69 197 325), lower := (rows 11 162 292 88 21 34 64 128 256), losses := [] }

theorem u17979 : Upper (D 6) (R 6) [10,160,288,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17980 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 162 292 88 21 36 67 195 323), lower := (rows 11 162 292 88 21 36 64 128 256), losses := [] }

theorem u17980 : Upper (D 6) (R 6) [10,160,288,80,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17981 : Route 9 := (fun mask => (mask,id))

def c17981 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17981 : Upper (D 6) (R 6) [10,160,288,80,5,64] 13 := by
  apply FastRouting.sound _ _ [10,160,288,80,5,64] 13 (by decide) (choices 1) [1,2,4] r17981 c17981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5206
  · exact u5207
  · exact u5208

def b17982 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 324 13 49 34 84 212 340), lower := (rows 11 162 324 13 49 34 64 128 256), losses := [] }

theorem u17982 : Upper (D 6) (R 6) [10,160,320,5,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17983 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 66 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 162 324 13 49 36 82 210 338), lower := (rows 11 162 324 13 49 36 64 128 256), losses := [] }

theorem u17983 : Upper (D 6) (R 6) [10,160,320,5,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17984 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 162 324 13 49 48 70 198 326), lower := (rows 11 162 324 13 49 48 64 128 256), losses := [] }

theorem u17984 : Upper (D 6) (R 6) [10,160,320,5,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17984 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17985 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 454, targets := 1 }], pairs := [(1,0),(2,0),(4,1)], upper := (rows 11 162 324 13 49 96 86 150 278), lower := (rows 11 162 324 13 49 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 100 64 128 256), good := (rows 25 160 356 61 49 96 96 128 256) }] }

theorem u17985 : Upper (D 6) (R 6) [10,160,320,5,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17986 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 324 13 52 33 82 210 338), lower := (rows 11 162 324 13 52 33 64 128 256), losses := [] }

theorem u17986 : Upper (D 6) (R 6) [10,160,320,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17987 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 324 13 52 34 81 209 337), lower := (rows 11 162 324 13 52 34 64 128 256), losses := [] }

theorem u17987 : Upper (D 6) (R 6) [10,160,320,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17988 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 324 13 52 48 67 195 323), lower := (rows 11 162 324 13 52 48 64 128 256), losses := [] }

theorem u17988 : Upper (D 6) (R 6) [10,160,320,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17988 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17989 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 324 13 52 96 83 147 275), lower := (rows 11 162 324 13 52 96 64 128 256), losses := [] }

theorem u17989 : Upper (D 6) (R 6) [10,160,320,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17990 : PairBound 9 := { available := 52, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 324 13 81 34 116 180 308), lower := (rows 11 162 324 13 81 34 64 128 256), losses := [] }

theorem u17990 : Upper (D 6) (R 6) [10,160,320,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17991 : Route 9 := (fun mask => (mask,id))

def c17991 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17991 : Upper (D 6) (R 6) [10,160,320,5,65,4] 13 := by
  apply FastRouting.sound _ _ [10,160,320,5,65,4] 13 (by decide) (choices 1) [2,16,32] r17991 c17991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5209
  · exact u5210
  · exact u5211

def b17992 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 324 13 81 48 102 166 294), lower := (rows 11 162 324 13 81 48 64 128 256), losses := [] }

theorem u17992 : Upper (D 6) (R 6) [10,160,320,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17992 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17993 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 324 13 82 33 116 180 308), lower := (rows 11 162 324 13 82 33 64 128 256), losses := [] }

theorem u17993 : Upper (D 6) (R 6) [10,160,320,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17994 : Route 9 := (fun mask => (mask,id))

def c17994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17994 : Upper (D 6) (R 6) [10,160,320,5,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,320,5,66,4] 13 (by decide) (choices 1) [1,16,32] r17994 c17994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5212
  · exact u5213
  · exact u5214

def r17995 : Route 9 := (fun mask => (mask,id))

def c17995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17995 : Upper (D 6) (R 6) [10,160,320,5,66,16] 13 := by
  apply FastRouting.sound _ _ [10,160,320,5,66,16] 13 (by decide) (choices 1) [1,4,32] r17995 c17995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5215
  · exact u5216
  · exact u5217

def b17996 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 324 13 112 33 86 150 278), lower := (rows 11 162 324 13 112 33 64 128 256), losses := [] }

theorem u17996 : Upper (D 6) (R 6) [10,160,320,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17997 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 324 13 112 34 85 149 277), lower := (rows 11 162 324 13 112 34 64 128 256), losses := [] }

theorem u17997 : Upper (D 6) (R 6) [10,160,320,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17998 : Route 9 := (fun mask => (mask,id))

def c17998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17998 : Upper (D 6) (R 6) [10,160,320,5,96,4] 13 := by
  apply FastRouting.sound _ _ [10,160,320,5,96,4] 13 (by decide) (choices 1) [1,2,16] r17998 c17998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5218
  · exact u5219
  · exact u5220

def b17999 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 324 13 112 48 71 135 263), lower := (rows 11 162 324 13 112 48 64 128 256), losses := [] }

theorem u17999 : Upper (D 6) (R 6) [10,160,320,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17999 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u17999
end Delivery.IrregularNine14.P06
