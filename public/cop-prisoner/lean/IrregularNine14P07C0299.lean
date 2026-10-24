import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0078
import IrregularNine14P07C0079

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r17940 : Route 9 := (fun mask => (mask,id))

def c17940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17940 : Upper (D 7) (R 7) [34,65,9,20,130,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,130,256] 13 (by decide) (choices 1) [32,128] r17940 c17940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4716
  · exact u4717

def b17941 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 28 176 34 448 448 448), lower := (rows 35 67 13 28 176 34 64 128 256), losses := [] }

theorem u17941 : Upper (D 7) (R 7) [34,65,9,20,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17942 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 28 176 96 450 386 386), lower := (rows 35 67 13 28 176 96 64 128 256), losses := [] }

theorem u17942 : Upper (D 7) (R 7) [34,65,9,20,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17943 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 28 176 160 322 450 322), lower := (rows 35 67 13 28 176 160 64 128 256), losses := [] }

theorem u17943 : Upper (D 7) (R 7) [34,65,9,20,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17944 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 208, targets := 1 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 28 176 288 194 194 450), lower := (rows 35 67 13 28 176 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 295 67 131 259), good := (rows 498 498 508 60 176 288 64 128 288) }] }

theorem u17944 : Upper (D 7) (R 7) [34,65,9,20,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17944 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17945 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 28 208 34 480 416 416), lower := (rows 35 67 13 28 208 34 64 128 256), losses := [] }

theorem u17945 : Upper (D 7) (R 7) [34,65,9,20,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17946 : PairBound 9 := { available := 290, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 0, region := 464, targets := 1 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,0)], upper := (rows 35 67 13 28 208 160 354 418 290), lower := (rows 35 67 13 28 208 160 64 128 256), losses := [] }

theorem u17946 : Upper (D 7) (R 7) [34,65,9,20,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17947 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 208, targets := 1 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 13 28 208 288 226 162 418), lower := (rows 35 67 13 28 208 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 295 67 131 259), good := (rows 498 498 508 60 208 288 64 128 288) }] }

theorem u17947 : Upper (D 7) (R 7) [34,65,9,20,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17947 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17948 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 28 274 96 224 160 416), lower := (rows 35 67 13 28 274 96 64 128 256), losses := [] }

theorem u17948 : Upper (D 7) (R 7) [34,65,9,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17949 : Route 9 := (fun mask => (mask,id))

def c17949 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17949 : Upper (D 7) (R 7) [34,65,9,20,258,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,258,128] 13 (by decide) (choices 1) [32,128] r17949 c17949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4718
  · exact u4719

def b17950 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 28 304 34 192 192 448), lower := (rows 35 67 13 28 304 34 64 128 256), losses := [] }

theorem u17950 : Upper (D 7) (R 7) [34,65,9,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17951 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 28 304 96 194 130 386), lower := (rows 35 67 13 28 304 96 64 128 256), losses := [] }

theorem u17951 : Upper (D 7) (R 7) [34,65,9,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17951 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17952 : Route 9 := (fun mask => (mask,id))

def c17952 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17952 : Upper (D 7) (R 7) [34,65,9,20,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,288,128] 13 (by decide) (choices 1) [2,128] r17952 c17952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4720
  · exact u4721

def b17953 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 28 336 34 224 160 416), lower := (rows 35 67 13 28 336 34 64 128 256), losses := [] }

theorem u17953 : Upper (D 7) (R 7) [34,65,9,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17954 : Route 9 := (fun mask => (mask,id))

def c17954 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17954 : Upper (D 7) (R 7) [34,65,9,20,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,320,128] 13 (by decide) (choices 1) [2,32,128] r17954 c17954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4722
  · exact u4723
  · exact u4724

def b17955 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 28 400 34 224 224 480), lower := (rows 35 67 13 28 400 34 64 128 256), losses := [] }

theorem u17955 : Upper (D 7) (R 7) [34,65,9,20,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17956 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 5, region := 3, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 28 400 96 226 162 418), lower := (rows 35 67 13 28 400 96 64 128 256), losses := [] }

theorem u17956 : Upper (D 7) (R 7) [34,65,9,20,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17957 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 67, targets := 128 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(4,0)], upper := (rows 35 67 13 28 400 160 98 226 354), lower := (rows 35 67 13 28 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 183 67 131 259), good := (rows 498 498 508 60 432 160 64 160 256) }] }

theorem u17957 : Upper (D 7) (R 7) [34,65,9,20,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17958 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 56 146 36 448 448 448), lower := (rows 35 67 13 56 146 36 64 128 256), losses := [] }

theorem u17958 : Upper (D 7) (R 7) [34,65,9,48,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17958 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17959 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 56 146 96 452 388 388), lower := (rows 35 67 13 56 146 96 64 128 256), losses := [] }

theorem u17959 : Upper (D 7) (R 7) [34,65,9,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17960 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 35 67 13 56 146 160 324 452 324), lower := (rows 35 67 13 56 146 160 64 128 256), losses := [] }

theorem u17960 : Upper (D 7) (R 7) [34,65,9,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17961 : Route 9 := (fun mask => (mask,id))

def c17961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17961 : Upper (D 7) (R 7) [34,65,9,48,130,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,130,256] 13 (by decide) (choices 1) [4,128] r17961 c17961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4725
  · exact u4726

def b17962 : PairBound 9 := { available := 388, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 56 208 34 452 388 388), lower := (rows 35 67 13 56 208 34 64 128 256), losses := [] }

theorem u17962 : Upper (D 7) (R 7) [34,65,9,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17963 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 56 208 36 450 386 386), lower := (rows 35 67 13 56 208 36 64 128 256), losses := [] }

theorem u17963 : Upper (D 7) (R 7) [34,65,9,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17963 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17964 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 67 13 56 208 160 326 390 262), lower := (rows 35 67 13 56 208 160 64 128 256), losses := [] }

theorem u17964 : Upper (D 7) (R 7) [34,65,9,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17965 : Route 9 := (fun mask => (mask,id))

def c17965 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17965 : Upper (D 7) (R 7) [34,65,9,48,192,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,192,256] 13 (by decide) (choices 1) [2,4,128] r17965 c17965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4727
  · exact u4728
  · exact u4729

def b17966 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 56 274 36 192 192 448), lower := (rows 35 67 13 56 274 36 64 128 256), losses := [] }

theorem u17966 : Upper (D 7) (R 7) [34,65,9,48,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17966 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17967 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 56 274 96 196 132 388), lower := (rows 35 67 13 56 274 96 64 128 256), losses := [] }

theorem u17967 : Upper (D 7) (R 7) [34,65,9,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17968 : Route 9 := (fun mask => (mask,id))

def c17968 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17968 : Upper (D 7) (R 7) [34,65,9,48,258,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,258,128] 13 (by decide) (choices 1) [4,128] r17968 c17968
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4730
  · exact u4731

def b17969 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 56 336 34 196 132 388), lower := (rows 35 67 13 56 336 34 64 128 256), losses := [] }

theorem u17969 : Upper (D 7) (R 7) [34,65,9,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17970 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 56 336 36 194 130 386), lower := (rows 35 67 13 56 336 36 64 128 256), losses := [] }

theorem u17970 : Upper (D 7) (R 7) [34,65,9,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17970 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17971 : Route 9 := (fun mask => (mask,id))

def c17971 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17971 : Upper (D 7) (R 7) [34,65,9,48,320,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,48,320,128] 13 (by decide) (choices 1) [2,4,128] r17971 c17971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4732
  · exact u4733
  · exact u4734

def b17972 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 56 400 34 196 196 452), lower := (rows 35 67 13 56 400 34 64 128 256), losses := [] }

theorem u17972 : Upper (D 7) (R 7) [34,65,9,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17973 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 56 400 36 194 194 450), lower := (rows 35 67 13 56 400 36 64 128 256), losses := [] }

theorem u17973 : Upper (D 7) (R 7) [34,65,9,48,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17973 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17974 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 67 13 56 400 96 198 134 390), lower := (rows 35 67 13 56 400 96 64 128 256), losses := [] }

theorem u17974 : Upper (D 7) (R 7) [34,65,9,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17975 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 67 13 56 400 160 70 198 326), lower := (rows 35 67 13 56 400 160 64 128 256), losses := [] }

theorem u17975 : Upper (D 7) (R 7) [34,65,9,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17975 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17976 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 88 146 36 480 416 416), lower := (rows 35 67 13 88 146 36 64 128 256), losses := [] }

theorem u17976 : Upper (D 7) (R 7) [34,65,9,80,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17976 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17977 : Route 9 := (fun mask => (mask,id))

def c17977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u17977 : Upper (D 7) (R 7) [34,65,9,80,130,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,130,128] 13 (by decide) (choices 1) [4,32,256] r17977 c17977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4735
  · exact u4736
  · exact u4737

def r17978 : Route 9 := (fun mask => (mask,id))

def c17978 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17978 : Upper (D 7) (R 7) [34,65,9,80,130,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,130,256] 13 (by decide) (choices 1) [4,32,128] r17978 c17978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4738
  · exact u4739
  · exact u4740

def b17979 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 88 176 34 452 388 388), lower := (rows 35 67 13 88 176 34 64 128 256), losses := [] }

theorem u17979 : Upper (D 7) (R 7) [34,65,9,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17980 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 88 176 36 450 386 386), lower := (rows 35 67 13 88 176 36 64 128 256), losses := [] }

theorem u17980 : Upper (D 7) (R 7) [34,65,9,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17980 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17981 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 67 13 88 176 160 326 390 262), lower := (rows 35 67 13 88 176 160 64 128 256), losses := [] }

theorem u17981 : Upper (D 7) (R 7) [34,65,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17982 : Route 9 := (fun mask => (mask,id))

def c17982 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17982 : Upper (D 7) (R 7) [34,65,9,80,160,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,160,256] 13 (by decide) (choices 1) [2,4,128] r17982 c17982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4741
  · exact u4742
  · exact u4743

def b17983 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 88 274 36 224 160 416), lower := (rows 35 67 13 88 274 36 64 128 256), losses := [] }

theorem u17983 : Upper (D 7) (R 7) [34,65,9,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17983 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17984 : Route 9 := (fun mask => (mask,id))

def c17984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u17984 : Upper (D 7) (R 7) [34,65,9,80,258,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,258,128] 13 (by decide) (choices 1) [4,32,128] r17984 c17984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4744
  · exact u4745
  · exact u4746

def b17985 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 88 304 34 196 132 388), lower := (rows 35 67 13 88 304 34 64 128 256), losses := [] }

theorem u17985 : Upper (D 7) (R 7) [34,65,9,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17986 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 88 304 36 194 130 386), lower := (rows 35 67 13 88 304 36 64 128 256), losses := [] }

theorem u17986 : Upper (D 7) (R 7) [34,65,9,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17986 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17987 : Route 9 := (fun mask => (mask,id))

def c17987 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17987 : Upper (D 7) (R 7) [34,65,9,80,288,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,288,128] 13 (by decide) (choices 1) [2,4,128] r17987 c17987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4747
  · exact u4748
  · exact u4749

def b17988 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 13 88 400 34 228 164 420), lower := (rows 35 67 13 88 400 34 64 128 256), losses := [] }

theorem u17988 : Upper (D 7) (R 7) [34,65,9,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17989 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 13 88 400 36 226 162 418), lower := (rows 35 67 13 88 400 36 64 128 256), losses := [] }

theorem u17989 : Upper (D 7) (R 7) [34,65,9,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17989 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17990 : Route 9 := (fun mask => (mask,id))

def c17990 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17990 : Upper (D 7) (R 7) [34,65,9,80,384,128] 13 := by
  apply FastRouting.sound _ _ [34,65,9,80,384,128] 13 (by decide) (choices 1) [2,4,32] r17990 c17990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4750
  · exact u4751
  · exact u4752

def b17991 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 53, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 138 52 48 448 448 448), lower := (rows 35 67 13 138 52 48 64 128 256), losses := [] }

theorem u17991 : Upper (D 7) (R 7) [34,65,9,130,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17991 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17992 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0),(4,6)], upper := (rows 35 67 13 138 52 96 464 400 400), lower := (rows 35 67 13 138 52 96 64 128 256), losses := [] }

theorem u17992 : Upper (D 7) (R 7) [34,65,9,130,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17993 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(0,6),(2,6),(4,0),(4,6)], upper := (rows 35 67 13 138 52 160 336 464 336), lower := (rows 35 67 13 138 52 160 64 128 256), losses := [] }

theorem u17993 : Upper (D 7) (R 7) [34,65,9,130,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17994 : Route 9 := (fun mask => (mask,id))

def c17994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u17994 : Upper (D 7) (R 7) [34,65,9,130,36,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,36,256] 13 (by decide) (choices 1) [16,128] r17994 c17994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4753
  · exact u4754

def b17995 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 496, targets := 1 }], pairs := [(2,6),(3,6),(4,0)], upper := (rows 35 67 13 138 84 48 480 416 416), lower := (rows 35 67 13 138 84 48 64 128 256), losses := [] }

theorem u17995 : Upper (D 7) (R 7) [34,65,9,130,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17995 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17996 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 496, targets := 3 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 67 13 138 84 160 368 432 304), lower := (rows 35 67 13 138 84 160 64 128 256), losses := [] }

theorem u17996 : Upper (D 7) (R 7) [34,65,9,130,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r17997 : Route 9 := (fun mask => (mask,id))

def c17997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u17997 : Upper (D 7) (R 7) [34,65,9,130,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,9,130,68,256] 13 (by decide) (choices 1) [16,32,128] r17997 c17997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4755
  · exact u4756
  · exact u4757

def b17998 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 67 13 138 176 36 336 464 336), lower := (rows 35 67 13 138 176 36 64 128 256), losses := [] }

theorem u17998 : Upper (D 7) (R 7) [34,65,9,130,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17998 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17999 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 67 13 138 176 48 324 452 324), lower := (rows 35 67 13 138 176 48 64 128 256), losses := [] }

theorem u17999 : Upper (D 7) (R 7) [34,65,9,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17999 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u17999
end Delivery.IrregularNine14.P07
