import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0122

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23940 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 13 336 48 71 135 263), lower := (rows 35 138 100 13 336 48 64 128 256), losses := [] }

theorem u23940 : Upper (D 6) (R 6) [34,136,96,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23940 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23941 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 100 14 81 33 340 404 276), lower := (rows 35 138 100 14 81 33 64 128 256), losses := [] }

theorem u23941 : Upper (D 6) (R 6) [34,136,96,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23942 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 100 14 81 36 337 401 273), lower := (rows 35 138 100 14 81 36 64 128 256), losses := [] }

theorem u23942 : Upper (D 6) (R 6) [34,136,96,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23943 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 14 81 48 325 389 261), lower := (rows 35 138 100 14 81 48 64 128 256), losses := [] }

theorem u23943 : Upper (D 6) (R 6) [34,136,96,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23943 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23944 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 100 14 81 288 85 149 277), lower := (rows 35 138 100 14 81 288 64 128 256), losses := [] }

theorem u23944 : Upper (D 6) (R 6) [34,136,96,6,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23944 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23945 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 100 14 273 33 84 212 340), lower := (rows 35 138 100 14 273 33 64 128 256), losses := [] }

theorem u23945 : Upper (D 6) (R 6) [34,136,96,6,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23946 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 100 14 273 36 81 209 337), lower := (rows 35 138 100 14 273 36 64 128 256), losses := [] }

theorem u23946 : Upper (D 6) (R 6) [34,136,96,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23947 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 100 14 273 48 69 197 325), lower := (rows 35 138 100 14 273 48 64 128 256), losses := [] }

theorem u23947 : Upper (D 6) (R 6) [34,136,96,6,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23947 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23948 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 14 273 96 85 149 277), lower := (rows 35 138 100 14 273 96 64 128 256), losses := [] }

theorem u23948 : Upper (D 6) (R 6) [34,136,96,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23949 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 100 14 276 33 81 209 337), lower := (rows 35 138 100 14 276 33 64 128 256), losses := [] }

theorem u23949 : Upper (D 6) (R 6) [34,136,96,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23950 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 100 14 276 48 65 193 321), lower := (rows 35 138 100 14 276 48 64 128 256), losses := [] }

theorem u23950 : Upper (D 6) (R 6) [34,136,96,6,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23950 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23951 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 14 276 96 81 145 273), lower := (rows 35 138 100 14 276 96 64 128 256), losses := [] }

theorem u23951 : Upper (D 6) (R 6) [34,136,96,6,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23952 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 100 14 336 33 85 149 277), lower := (rows 35 138 100 14 336 33 64 128 256), losses := [] }

theorem u23952 : Upper (D 6) (R 6) [34,136,96,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23953 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 138 100 14 336 36 81 145 273), lower := (rows 35 138 100 14 336 36 64 128 256), losses := [] }

theorem u23953 : Upper (D 6) (R 6) [34,136,96,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23954 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 14 336 48 69 133 261), lower := (rows 35 138 100 14 336 48 64 128 256), losses := [] }

theorem u23954 : Upper (D 6) (R 6) [34,136,96,6,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23954 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23955 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 138 100 25 22 33 324 452 324), lower := (rows 35 138 100 25 22 33 64 128 256), losses := [] }

theorem u23955 : Upper (D 6) (R 6) [34,136,96,17,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23956 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 450, targets := 36 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(1,2),(1,5)], upper := (rows 35 138 100 25 22 36 321 449 321), lower := (rows 35 138 100 25 22 36 64 128 256), losses := [] }

theorem u23956 : Upper (D 6) (R 6) [34,136,96,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23957 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 25 22 96 325 389 261), lower := (rows 35 138 100 25 22 96 64 128 256), losses := [] }

theorem u23957 : Upper (D 6) (R 6) [34,136,96,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23958 : Route 9 := (fun mask => (mask,id))

def c23958 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23958 : Upper (D 6) (R 6) [34,136,96,17,6,256] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17,6,256] 13 (by decide) (choices 1) [1,4] r23958 c23958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7365
  · exact u7366

def b23959 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 138 100 25 82 33 324 388 260), lower := (rows 35 138 100 25 82 33 64 128 256), losses := [] }

theorem u23959 : Upper (D 6) (R 6) [34,136,96,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23960 : Route 9 := (fun mask => (mask,id))

def c23960 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23960 : Upper (D 6) (R 6) [34,136,96,17,66,4] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17,66,4] 13 (by decide) (choices 1) [1,4,256] r23960 c23960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7367
  · exact u7368
  · exact u7369

def r23961 : Route 9 := (fun mask => (mask,id))

def c23961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23961 : Upper (D 6) (R 6) [34,136,96,17,66,256] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17,66,256] 13 (by decide) (choices 1) [1,4] r23961 c23961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7370
  · exact u7371

def b23962 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 138 100 25 274 33 68 196 324), lower := (rows 35 138 100 25 274 33 64 128 256), losses := [] }

theorem u23962 : Upper (D 6) (R 6) [34,136,96,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23963 : Route 9 := (fun mask => (mask,id))

def c23963 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23963 : Upper (D 6) (R 6) [34,136,96,17,258,4] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17,258,4] 13 (by decide) (choices 1) [1,4] r23963 c23963
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7372
  · exact u7373

def b23964 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 25 274 96 69 133 261), lower := (rows 35 138 100 25 274 96 64 128 256), losses := [] }

theorem u23964 : Upper (D 6) (R 6) [34,136,96,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23964 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23965 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 100 25 276 33 70 198 326), lower := (rows 35 138 100 25 276 33 64 128 256), losses := [] }

theorem u23965 : Upper (D 6) (R 6) [34,136,96,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23966 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 25 276 34 69 197 325), lower := (rows 35 138 100 25 276 34 64 128 256), losses := [] }

theorem u23966 : Upper (D 6) (R 6) [34,136,96,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23967 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 194, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 138 100 25 276 36 67 195 323), lower := (rows 35 138 100 25 276 36 64 128 256), losses := [] }

theorem u23967 : Upper (D 6) (R 6) [34,136,96,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23968 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 25 276 96 71 135 263), lower := (rows 35 138 100 25 276 96 64 128 256), losses := [] }

theorem u23968 : Upper (D 6) (R 6) [34,136,96,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23969 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 100 25 336 33 70 134 262), lower := (rows 35 138 100 25 336 33 64 128 256), losses := [] }

theorem u23969 : Upper (D 6) (R 6) [34,136,96,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23970 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 25 336 34 69 133 261), lower := (rows 35 138 100 25 336 34 64 128 256), losses := [] }

theorem u23970 : Upper (D 6) (R 6) [34,136,96,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23971 : Route 9 := (fun mask => (mask,id))

def c23971 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23971 : Upper (D 6) (R 6) [34,136,96,17,320,4] 13 := by
  apply FastRouting.sound _ _ [34,136,96,17,320,4] 13 (by decide) (choices 1) [1,2,4] r23971 c23971
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7374
  · exact u7375
  · exact u7376

def b23972 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 100 26 81 33 324 388 260), lower := (rows 35 138 100 26 81 33 64 128 256), losses := [] }

theorem u23972 : Upper (D 6) (R 6) [34,136,96,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23973 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 100 26 81 36 325 389 261), lower := (rows 35 138 100 26 81 36 64 128 256), losses := [] }

theorem u23973 : Upper (D 6) (R 6) [34,136,96,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23974 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 100 26 81 288 69 133 261), lower := (rows 35 138 100 26 81 288 64 128 256), losses := [] }

theorem u23974 : Upper (D 6) (R 6) [34,136,96,18,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23974 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23975 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 100 26 273 33 68 196 324), lower := (rows 35 138 100 26 273 33 64 128 256), losses := [] }

theorem u23975 : Upper (D 6) (R 6) [34,136,96,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23976 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 100 26 273 36 69 197 325), lower := (rows 35 138 100 26 273 36 64 128 256), losses := [] }

theorem u23976 : Upper (D 6) (R 6) [34,136,96,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23977 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 26 273 96 69 133 261), lower := (rows 35 138 100 26 273 96 64 128 256), losses := [] }

theorem u23977 : Upper (D 6) (R 6) [34,136,96,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23978 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 100 26 276 33 69 197 325), lower := (rows 35 138 100 26 276 33 64 128 256), losses := [] }

theorem u23978 : Upper (D 6) (R 6) [34,136,96,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23979 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 100 26 276 36 65 193 321), lower := (rows 35 138 100 26 276 36 64 128 256), losses := [] }

theorem u23979 : Upper (D 6) (R 6) [34,136,96,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23980 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 26 276 96 69 133 261), lower := (rows 35 138 100 26 276 96 64 128 256), losses := [] }

theorem u23980 : Upper (D 6) (R 6) [34,136,96,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23980 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23981 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 100 26 336 33 69 133 261), lower := (rows 35 138 100 26 336 33 64 128 256), losses := [] }

theorem u23981 : Upper (D 6) (R 6) [34,136,96,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23982 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 138 100 26 336 36 69 133 261), lower := (rows 35 138 100 26 336 36 64 128 256), losses := [] }

theorem u23982 : Upper (D 6) (R 6) [34,136,96,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23983 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 386, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 138 100 28 81 33 326 390 262), lower := (rows 35 138 100 28 81 33 64 128 256), losses := [] }

theorem u23983 : Upper (D 6) (R 6) [34,136,96,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23984 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 28 81 34 325 389 261), lower := (rows 35 138 100 28 81 34 64 128 256), losses := [] }

theorem u23984 : Upper (D 6) (R 6) [34,136,96,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23985 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 138 100 28 81 36 323 387 259), lower := (rows 35 138 100 28 81 36 64 128 256), losses := [] }

theorem u23985 : Upper (D 6) (R 6) [34,136,96,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23986 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 100 28 81 288 71 135 263), lower := (rows 35 138 100 28 81 288 64 128 256), losses := [] }

theorem u23986 : Upper (D 6) (R 6) [34,136,96,20,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23986 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23987 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 138 100 28 273 33 70 198 326), lower := (rows 35 138 100 28 273 33 64 128 256), losses := [] }

theorem u23987 : Upper (D 6) (R 6) [34,136,96,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23988 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 28 273 34 69 197 325), lower := (rows 35 138 100 28 273 34 64 128 256), losses := [] }

theorem u23988 : Upper (D 6) (R 6) [34,136,96,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23989 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 138 100 28 273 36 67 195 323), lower := (rows 35 138 100 28 273 36 64 128 256), losses := [] }

theorem u23989 : Upper (D 6) (R 6) [34,136,96,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23990 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 28 273 96 71 135 263), lower := (rows 35 138 100 28 273 96 64 128 256), losses := [] }

theorem u23990 : Upper (D 6) (R 6) [34,136,96,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23991 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 68, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 138 100 28 274 33 69 197 325), lower := (rows 35 138 100 28 274 33 64 128 256), losses := [] }

theorem u23991 : Upper (D 6) (R 6) [34,136,96,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23992 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 35 138 100 28 274 36 65 193 321), lower := (rows 35 138 100 28 274 36 64 128 256), losses := [] }

theorem u23992 : Upper (D 6) (R 6) [34,136,96,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23993 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 35 138 100 28 274 96 69 133 261), lower := (rows 35 138 100 28 274 96 64 128 256), losses := [] }

theorem u23993 : Upper (D 6) (R 6) [34,136,96,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23994 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 163, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 138 100 28 336 33 71 135 263), lower := (rows 35 138 100 28 336 33 64 128 256), losses := [] }

theorem u23994 : Upper (D 6) (R 6) [34,136,96,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23994 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23995 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 28 336 34 69 133 261), lower := (rows 35 138 100 28 336 34 64 128 256), losses := [] }

theorem u23995 : Upper (D 6) (R 6) [34,136,96,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23996 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 138 100 28 336 36 67 131 259), lower := (rows 35 138 100 28 336 36 64 128 256), losses := [] }

theorem u23996 : Upper (D 6) (R 6) [34,136,96,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23997 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 100 73 21 34 340 404 276), lower := (rows 35 138 100 73 21 34 64 128 256), losses := [] }

theorem u23997 : Upper (D 6) (R 6) [34,136,96,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23998 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 100 73 21 36 338 402 274), lower := (rows 35 138 100 73 21 36 64 128 256), losses := [] }

theorem u23998 : Upper (D 6) (R 6) [34,136,96,65,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23998 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23999 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 52, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 100 73 21 48 326 390 262), lower := (rows 35 138 100 73 21 48 64 128 256), losses := [] }

theorem u23999 : Upper (D 6) (R 6) [34,136,96,65,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23999 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23999
end Delivery.IrregularNine14.P06
