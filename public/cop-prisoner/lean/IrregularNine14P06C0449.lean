import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0141

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26940 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 41 134 324 88 52 33 67 131 259), lower := (rows 41 134 324 88 52 33 64 128 256), losses := [] }

theorem u26940 : Upper (D 6) (R 6) [40,132,320,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26941 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(4,0)], upper := (rows 41 134 324 88 52 34 67 131 259), lower := (rows 41 134 324 88 52 34 64 128 256), losses := [] }

theorem u26941 : Upper (D 6) (R 6) [40,132,320,80,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26942 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 292 11 22 33 68 196 324), lower := (rows 41 146 292 11 22 33 64 128 256), losses := [] }

theorem u26942 : Upper (D 6) (R 6) [40,144,288,3,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26943 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 146 292 11 22 36 65 193 321), lower := (rows 41 146 292 11 22 36 64 128 256), losses := [] }

theorem u26943 : Upper (D 6) (R 6) [40,144,288,3,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26944 : Route 9 := (fun mask => (mask,id))

def c26944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26944 : Upper (D 6) (R 6) [40,144,288,3,6,64] 13 := by
  apply FastRouting.sound _ _ [40,144,288,3,6,64] 13 (by decide) (choices 1) [1,4] r26944 c26944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8470
  · exact u8471

def b26945 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 292 11 81 34 68 196 324), lower := (rows 41 146 292 11 81 34 64 128 256), losses := [] }

theorem u26945 : Upper (D 6) (R 6) [40,144,288,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26946 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 146 292 11 81 36 70 198 326), lower := (rows 41 146 292 11 81 36 64 128 256), losses := [] }

theorem u26946 : Upper (D 6) (R 6) [40,144,288,3,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26947 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 41 146 292 11 81 96 70 134 262), lower := (rows 41 146 292 11 81 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 10 16 112 64 128 256), good := (rows 41 187 288 11 113 96 96 128 256) }] }

theorem u26947 : Upper (D 6) (R 6) [40,144,288,3,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26948 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 292 11 82 33 68 196 324), lower := (rows 41 146 292 11 82 33 64 128 256), losses := [] }

theorem u26948 : Upper (D 6) (R 6) [40,144,288,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26949 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 146 292 11 82 36 69 197 325), lower := (rows 41 146 292 11 82 36 64 128 256), losses := [] }

theorem u26949 : Upper (D 6) (R 6) [40,144,288,3,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26950 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 41 146 292 11 82 96 69 133 261), lower := (rows 41 146 292 11 82 96 64 128 256), losses := [] }

theorem u26950 : Upper (D 6) (R 6) [40,144,288,3,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26951 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 292 11 84 33 70 198 326), lower := (rows 41 146 292 11 84 33 64 128 256), losses := [] }

theorem u26951 : Upper (D 6) (R 6) [40,144,288,3,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26952 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 146 292 11 84 34 69 197 325), lower := (rows 41 146 292 11 84 34 64 128 256), losses := [] }

theorem u26952 : Upper (D 6) (R 6) [40,144,288,3,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26953 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 146 292 11 84 36 67 195 323), lower := (rows 41 146 292 11 84 36 64 128 256), losses := [] }

theorem u26953 : Upper (D 6) (R 6) [40,144,288,3,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26954 : PairBound 9 := { available := 7, camps := [], pairs := [(0,2),(2,6),(3,2)], upper := (rows 41 146 292 11 84 96 71 135 263), lower := (rows 41 146 292 11 84 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 10 16 112 64 128 256), good := (rows 41 187 288 11 112 96 96 128 256) },{ target := 6, region := (rows 1 2 5 8 16 32 0 136 264), good := (rows 429 146 292 399 20 32 0 128 256) }] }

theorem u26954 : Upper (D 6) (R 6) [40,144,288,3,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26955 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 146 292 14 19 33 68 196 324), lower := (rows 41 146 292 14 19 33 64 128 256), losses := [] }

theorem u26955 : Upper (D 6) (R 6) [40,144,288,6,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26956 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 146 292 14 19 36 65 193 321), lower := (rows 41 146 292 14 19 36 64 128 256), losses := [] }

theorem u26956 : Upper (D 6) (R 6) [40,144,288,6,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26957 : Route 9 := (fun mask => (mask,id))

def c26957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26957 : Upper (D 6) (R 6) [40,144,288,6,3,64] 13 := by
  apply FastRouting.sound _ _ [40,144,288,6,3,64] 13 (by decide) (choices 1) [1,4] r26957 c26957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8472
  · exact u8473

def b26958 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 146 292 14 81 33 70 198 326), lower := (rows 41 146 292 14 81 33 64 128 256), losses := [] }

theorem u26958 : Upper (D 6) (R 6) [40,144,288,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26959 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 146 292 14 81 34 69 197 325), lower := (rows 41 146 292 14 81 34 64 128 256), losses := [] }

theorem u26959 : Upper (D 6) (R 6) [40,144,288,6,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26960 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 146 292 14 81 36 67 195 323), lower := (rows 41 146 292 14 81 36 64 128 256), losses := [] }

theorem u26960 : Upper (D 6) (R 6) [40,144,288,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26961 : Route 9 := (fun mask => (mask,id))

def c26961 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26961 : Upper (D 6) (R 6) [40,144,288,6,65,64] 13 := by
  apply FastRouting.sound _ _ [40,144,288,6,65,64] 13 (by decide) (choices 1) [1,2,4] r26961 c26961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8474
  · exact u8475
  · exact u8476

def b26962 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 41 146 292 14 82 33 69 197 325), lower := (rows 41 146 292 14 82 33 64 128 256), losses := [] }

theorem u26962 : Upper (D 6) (R 6) [40,144,288,6,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26963 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 146 292 14 82 36 65 193 321), lower := (rows 41 146 292 14 82 36 64 128 256), losses := [] }

theorem u26963 : Upper (D 6) (R 6) [40,144,288,6,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26964 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 357, targets := 2 },{ cop := 0, region := 260, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 41 146 292 14 82 96 69 133 261), lower := (rows 41 146 292 14 82 96 64 128 256), losses := [] }

theorem u26964 : Upper (D 6) (R 6) [40,144,288,6,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26965 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 146 292 14 84 33 67 195 323), lower := (rows 41 146 292 14 84 33 64 128 256), losses := [] }

theorem u26965 : Upper (D 6) (R 6) [40,144,288,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26966 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 146 292 14 84 34 65 193 321), lower := (rows 41 146 292 14 84 34 64 128 256), losses := [] }

theorem u26966 : Upper (D 6) (R 6) [40,144,288,6,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26967 : Route 9 := (fun mask => (mask,id))

def c26967 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26967 : Upper (D 6) (R 6) [40,144,288,6,68,64] 13 := by
  apply FastRouting.sound _ _ [40,144,288,6,68,64] 13 (by decide) (choices 1) [1,2] r26967 c26967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8477
  · exact u8478

def b26968 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 333, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 292 73 19 34 68 196 324), lower := (rows 41 146 292 73 19 34 64 128 256), losses := [] }

theorem u26968 : Upper (D 6) (R 6) [40,144,288,65,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26969 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 146 292 73 19 36 70 198 326), lower := (rows 41 146 292 73 19 36 64 128 256), losses := [] }

theorem u26969 : Upper (D 6) (R 6) [40,144,288,65,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26970 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 146 292 73 19 96 70 134 262), lower := (rows 41 146 292 73 19 96 64 128 256), losses := [] }

theorem u26970 : Upper (D 6) (R 6) [40,144,288,65,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26971 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 146 292 73 22 33 70 198 326), lower := (rows 41 146 292 73 22 33 64 128 256), losses := [] }

theorem u26971 : Upper (D 6) (R 6) [40,144,288,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26972 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 333, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 292 73 22 34 69 197 325), lower := (rows 41 146 292 73 22 34 64 128 256), losses := [] }

theorem u26972 : Upper (D 6) (R 6) [40,144,288,65,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26973 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 146 292 73 22 36 67 195 323), lower := (rows 41 146 292 73 22 36 64 128 256), losses := [] }

theorem u26973 : Upper (D 6) (R 6) [40,144,288,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26974 : PairBound 9 := { available := 7, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 146 292 73 22 96 71 135 263), lower := (rows 41 146 292 73 22 96 64 128 256), losses := [] }

theorem u26974 : Upper (D 6) (R 6) [40,144,288,65,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26975 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 146 292 73 82 33 70 134 262), lower := (rows 41 146 292 73 82 33 64 128 256), losses := [] }

theorem u26975 : Upper (D 6) (R 6) [40,144,288,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26976 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 333, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 292 73 82 34 69 133 261), lower := (rows 41 146 292 73 82 34 64 128 256), losses := [] }

theorem u26976 : Upper (D 6) (R 6) [40,144,288,65,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26977 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 146 292 73 82 36 71 135 263), lower := (rows 41 146 292 73 82 36 64 128 256), losses := [] }

theorem u26977 : Upper (D 6) (R 6) [40,144,288,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26978 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 146 292 73 84 33 70 134 262), lower := (rows 41 146 292 73 84 33 64 128 256), losses := [] }

theorem u26978 : Upper (D 6) (R 6) [40,144,288,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26979 : Route 9 := (fun mask => (mask,id))

def c26979 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26979 : Upper (D 6) (R 6) [40,144,288,65,68,2] 13 := by
  apply FastRouting.sound _ _ [40,144,288,65,68,2] 13 (by decide) (choices 1) [1,2,4] r26979 c26979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8479
  · exact u8480
  · exact u8481

def b26980 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 146 292 73 84 36 67 131 259), lower := (rows 41 146 292 73 84 36 64 128 256), losses := [] }

theorem u26980 : Upper (D 6) (R 6) [40,144,288,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26981 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 41 146 292 74 19 33 68 196 324), lower := (rows 41 146 292 74 19 33 64 128 256), losses := [] }

theorem u26981 : Upper (D 6) (R 6) [40,144,288,66,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26982 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 146 292 74 19 36 69 197 325), lower := (rows 41 146 292 74 19 36 64 128 256), losses := [] }

theorem u26982 : Upper (D 6) (R 6) [40,144,288,66,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26983 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 146 292 74 19 96 69 133 261), lower := (rows 41 146 292 74 19 96 64 128 256), losses := [] }

theorem u26983 : Upper (D 6) (R 6) [40,144,288,66,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26984 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 41 146 292 74 21 33 70 198 326), lower := (rows 41 146 292 74 21 33 64 128 256), losses := [] }

theorem u26984 : Upper (D 6) (R 6) [40,144,288,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26985 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 146 292 74 21 34 69 197 325), lower := (rows 41 146 292 74 21 34 64 128 256), losses := [] }

theorem u26985 : Upper (D 6) (R 6) [40,144,288,66,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26986 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 41 146 292 74 21 36 67 195 323), lower := (rows 41 146 292 74 21 36 64 128 256), losses := [] }

theorem u26986 : Upper (D 6) (R 6) [40,144,288,66,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26987 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 146 292 74 21 96 71 135 263), lower := (rows 41 146 292 74 21 96 64 128 256), losses := [] }

theorem u26987 : Upper (D 6) (R 6) [40,144,288,66,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26988 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 293, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(2,1)], upper := (rows 41 146 292 74 22 33 69 197 325), lower := (rows 41 146 292 74 22 33 64 128 256), losses := [] }

theorem u26988 : Upper (D 6) (R 6) [40,144,288,66,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26989 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 146 292 74 22 36 65 193 321), lower := (rows 41 146 292 74 22 36 64 128 256), losses := [] }

theorem u26989 : Upper (D 6) (R 6) [40,144,288,66,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26990 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 146 292 74 22 96 69 133 261), lower := (rows 41 146 292 74 22 96 64 128 256), losses := [] }

theorem u26990 : Upper (D 6) (R 6) [40,144,288,66,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26991 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 146 292 74 84 33 71 135 263), lower := (rows 41 146 292 74 84 33 64 128 256), losses := [] }

theorem u26991 : Upper (D 6) (R 6) [40,144,288,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26992 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 41 146 292 74 84 34 69 133 261), lower := (rows 41 146 292 74 84 34 64 128 256), losses := [] }

theorem u26992 : Upper (D 6) (R 6) [40,144,288,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26993 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 146 292 74 84 36 67 131 259), lower := (rows 41 146 292 74 84 36 64 128 256), losses := [] }

theorem u26993 : Upper (D 6) (R 6) [40,144,288,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26994 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 146 292 76 19 33 70 198 326), lower := (rows 41 146 292 76 19 33 64 128 256), losses := [] }

theorem u26994 : Upper (D 6) (R 6) [40,144,288,68,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26995 : PairBound 9 := { available := 69, camps := [{ cop := 5, region := 333, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 292 76 19 34 69 197 325), lower := (rows 41 146 292 76 19 34 64 128 256), losses := [] }

theorem u26995 : Upper (D 6) (R 6) [40,144,288,68,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26996 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 210, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 41 146 292 76 19 36 67 195 323), lower := (rows 41 146 292 76 19 36 64 128 256), losses := [] }

theorem u26996 : Upper (D 6) (R 6) [40,144,288,68,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26997 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 146 292 76 19 96 71 135 263), lower := (rows 41 146 292 76 19 96 64 128 256), losses := [] }

theorem u26997 : Upper (D 6) (R 6) [40,144,288,68,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26998 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 146 292 76 22 33 67 195 323), lower := (rows 41 146 292 76 22 33 64 128 256), losses := [] }

theorem u26998 : Upper (D 6) (R 6) [40,144,288,68,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26999 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 333, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 146 292 76 22 34 65 193 321), lower := (rows 41 146 292 76 22 34 64 128 256), losses := [] }

theorem u26999 : Upper (D 6) (R 6) [40,144,288,68,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u26999
end Delivery.IrregularNine14.P06
