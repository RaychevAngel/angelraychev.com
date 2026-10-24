import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0192

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29940 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 164 13 276 98 98 226 354), lower := (rows 11 19 164 13 276 32 64 128 256), losses := [] }

theorem u29940 : Upper (D 6) (R 6) [10,17,160,5,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29940
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29941 : Route 9 := (fun mask => (mask,id))

def c29941 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29941 : Upper (D 6) (R 6) [10,17,160,5,288] 13 := by
  apply FastRouting.sound _ _ [10,17,160,5,288] 13 (by decide) (choices 1) [2,4,64] r29941 c29941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11522
  · exact u11523
  · exact u11524

def r29942 : Route 9 := (fun mask => (mask,id))

def c29942 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29942 : Upper (D 6) (R 6) [10,17,160,5,320] 13 := by
  apply FastRouting.sound _ _ [10,17,160,5,320] 13 (by decide) (choices 1) [2,4,64] r29942 c29942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11525
  · exact u11526
  · exact u11527

def b29943 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 164 14 84 353 353 481 353), lower := (rows 11 19 164 14 84 32 64 128 256), losses := [] }

theorem u29943 : Upper (D 6) (R 6) [10,17,160,6,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29943
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29944 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 19 164 14 112 357 325 453 325), lower := (rows 11 19 164 14 112 32 64 128 256), losses := [] }

theorem u29944 : Upper (D 6) (R 6) [10,17,160,6,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29944
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29945 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 164 14 276 97 97 225 353), lower := (rows 11 19 164 14 276 32 64 128 256), losses := [] }

theorem u29945 : Upper (D 6) (R 6) [10,17,160,6,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29945
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29946 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 11 19 164 14 304 101 69 197 325), lower := (rows 11 19 164 14 304 32 64 128 256), losses := [] }

theorem u29946 : Upper (D 6) (R 6) [10,17,160,6,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29946
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29947 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 14 336 101 101 229 357), lower := (rows 11 19 164 14 336 32 64 128 256), losses := [] }

theorem u29947 : Upper (D 6) (R 6) [10,17,160,6,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29947
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29948 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 41 82 356 324 452 324), lower := (rows 11 19 164 41 82 32 64 128 256), losses := [] }

theorem u29948 : Upper (D 6) (R 6) [10,17,160,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29948
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29949 : Route 9 := (fun mask => (mask,id))

def c29949 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u29949 : Upper (D 6) (R 6) [10,17,160,33,68] 13 := by
  apply FastRouting.sound _ _ [10,17,160,33,68] 13 (by decide) (choices 1) [2,4,64,256] r29949 c29949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11528
  · exact u11529
  · exact u11530
  · exact u11531

def b29950 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 41 274 100 68 196 324), lower := (rows 11 19 164 41 274 32 64 128 256), losses := [] }

theorem u29950 : Upper (D 6) (R 6) [10,17,160,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29950
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29951 : Route 9 := (fun mask => (mask,id))

def c29951 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29951 : Upper (D 6) (R 6) [10,17,160,33,260] 13 := by
  apply FastRouting.sound _ _ [10,17,160,33,260] 13 (by decide) (choices 1) [2,4,64] r29951 c29951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11532
  · exact u11533
  · exact u11534

def r29952 : Route 9 := (fun mask => (mask,id))

def c29952 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29952 : Upper (D 6) (R 6) [10,17,160,33,320] 13 := by
  apply FastRouting.sound _ _ [10,17,160,33,320] 13 (by decide) (choices 1) [2,4,64] r29952 c29952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11535
  · exact u11536
  · exact u11537

def b29953 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 42 84 357 325 453 325), lower := (rows 11 19 164 42 84 32 64 128 256), losses := [] }

theorem u29953 : Upper (D 6) (R 6) [10,17,160,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29953
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29954 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 42 276 101 69 197 325), lower := (rows 11 19 164 42 276 32 64 128 256), losses := [] }

theorem u29954 : Upper (D 6) (R 6) [10,17,160,34,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29954
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29955 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 42 336 101 69 197 325), lower := (rows 11 19 164 42 336 32 64 128 256), losses := [] }

theorem u29955 : Upper (D 6) (R 6) [10,17,160,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29955
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29956 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 164 44 82 357 325 453 325), lower := (rows 11 19 164 44 82 32 64 128 256), losses := [] }

theorem u29956 : Upper (D 6) (R 6) [10,17,160,36,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29956
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29957 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 164 44 84 355 323 451 323), lower := (rows 11 19 164 44 84 32 64 128 256), losses := [] }

theorem u29957 : Upper (D 6) (R 6) [10,17,160,36,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29957
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29958 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 164 44 274 101 69 197 325), lower := (rows 11 19 164 44 274 32 64 128 256), losses := [] }

theorem u29958 : Upper (D 6) (R 6) [10,17,160,36,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29958
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29959 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 164 44 276 99 67 195 323), lower := (rows 11 19 164 44 276 32 64 128 256), losses := [] }

theorem u29959 : Upper (D 6) (R 6) [10,17,160,36,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29959
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29960 : PairBound 9 := { available := 71, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 164 44 336 103 71 199 327), lower := (rows 11 19 164 44 336 32 64 128 256), losses := [] }

theorem u29960 : Upper (D 6) (R 6) [10,17,160,36,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29960
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29961 : PairBound 9 := { available := 292, camps := [{ cop := 6, region := 27, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 164 73 82 292 356 420 292), lower := (rows 11 19 164 73 82 32 64 128 256), losses := [] }

theorem u29961 : Upper (D 6) (R 6) [10,17,160,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29961
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29962 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 11, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 164 73 84 294 358 422 294), lower := (rows 11 19 164 73 84 32 64 128 256), losses := [] }

theorem u29962 : Upper (D 6) (R 6) [10,17,160,65,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29962
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29963 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 11, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 164 73 112 294 326 390 262), lower := (rows 11 19 164 73 112 32 64 128 256), losses := [] }

theorem u29963 : Upper (D 6) (R 6) [10,17,160,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29963
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29964 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 73 274 100 100 228 356), lower := (rows 11 19 164 73 274 32 64 128 256), losses := [] }

theorem u29964 : Upper (D 6) (R 6) [10,17,160,65,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29964
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29965 : Route 9 := (fun mask => (mask,id))

def c29965 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29965 : Upper (D 6) (R 6) [10,17,160,65,260] 13 := by
  apply FastRouting.sound _ _ [10,17,160,65,260] 13 (by decide) (choices 1) [2,4,64] r29965 c29965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11538
  · exact u11539
  · exact u11540

def r29966 : Route 9 := (fun mask => (mask,id))

def c29966 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29966 : Upper (D 6) (R 6) [10,17,160,65,288] 13 := by
  apply FastRouting.sound _ _ [10,17,160,65,288] 13 (by decide) (choices 1) [2,4,64] r29966 c29966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11541
  · exact u11542
  · exact u11543

def b29967 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 11, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 164 73 336 38 102 166 294), lower := (rows 11 19 164 73 336 32 64 128 256), losses := [] }

theorem u29967 : Upper (D 6) (R 6) [10,17,160,65,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29967
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29968 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 11, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 164 74 84 293 357 421 293), lower := (rows 11 19 164 74 84 32 64 128 256), losses := [] }

theorem u29968 : Upper (D 6) (R 6) [10,17,160,66,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29968
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29969 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 11, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 164 74 112 293 325 389 261), lower := (rows 11 19 164 74 112 32 64 128 256), losses := [] }

theorem u29969 : Upper (D 6) (R 6) [10,17,160,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29969
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29970 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 74 276 101 101 229 357), lower := (rows 11 19 164 74 276 32 64 128 256), losses := [] }

theorem u29970 : Upper (D 6) (R 6) [10,17,160,66,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29970
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29971 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 164 74 304 101 69 197 325), lower := (rows 11 19 164 74 304 32 64 128 256), losses := [] }

theorem u29971 : Upper (D 6) (R 6) [10,17,160,66,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29971
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29972 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 11, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 164 74 336 37 101 165 293), lower := (rows 11 19 164 74 336 32 64 128 256), losses := [] }

theorem u29972 : Upper (D 6) (R 6) [10,17,160,66,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29972
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29973 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 19, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 19 164 76 84 291 355 419 291), lower := (rows 11 19 164 76 84 32 64 128 256), losses := [] }

theorem u29973 : Upper (D 6) (R 6) [10,17,160,68,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29973
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29974 : Route 9 := (fun mask => (mask,id))

def c29974 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u29974 : Upper (D 6) (R 6) [10,17,160,68,96] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,96] 13 (by decide) (choices 1) [1,2,4,256] r29974 c29974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11544
  · exact u11545
  · exact u11546
  · exact u11547

def b29975 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 2, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 11 19 164 76 273 102 102 230 358), lower := (rows 11 19 164 76 273 32 64 128 256), losses := [] }

theorem u29975 : Upper (D 6) (R 6) [10,17,160,68,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29975
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29976 : Route 9 := (fun mask => (mask,id))

def c29976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29976 : Upper (D 6) (R 6) [10,17,160,68,258] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,258] 13 (by decide) (choices 1) [1,4,64] r29976 c29976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11548
  · exact u11549
  · exact u11550

def r29977 : Route 9 := (fun mask => (mask,id))

def c29977 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29977 : Upper (D 6) (R 6) [10,17,160,68,260] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,260] 13 (by decide) (choices 1) [1,2,64] r29977 c29977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11551
  · exact u11552
  · exact u11553

def r29978 : Route 9 := (fun mask => (mask,id))

def c29978 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29978 : Upper (D 6) (R 6) [10,17,160,68,288] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,288] 13 (by decide) (choices 1) [1,2,4,64] r29978 c29978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11554
  · exact u11555
  · exact u11556
  · exact u11557

def r29979 : Route 9 := (fun mask => (mask,id))

def c29979 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29979 : Upper (D 6) (R 6) [10,17,160,68,320] 13 := by
  apply FastRouting.sound _ _ [10,17,160,68,320] 13 (by decide) (choices 1) [1,2,4] r29979 c29979
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11558
  · exact u11559
  · exact u11560

def b29980 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 2, targets := 100 }], pairs := [(1,2),(1,5),(1,6)], upper := (rows 11 19 164 104 273 102 70 198 326), lower := (rows 11 19 164 104 273 32 64 128 256), losses := [] }

theorem u29980 : Upper (D 6) (R 6) [10,17,160,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29980
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29981 : Route 9 := (fun mask => (mask,id))

def c29981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29981 : Upper (D 6) (R 6) [10,17,160,96,258] 13 := by
  apply FastRouting.sound _ _ [10,17,160,96,258] 13 (by decide) (choices 1) [1,4,64] r29981 c29981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11561
  · exact u11562
  · exact u11563

def r29982 : Route 9 := (fun mask => (mask,id))

def c29982 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29982 : Upper (D 6) (R 6) [10,17,160,96,260] 13 := by
  apply FastRouting.sound _ _ [10,17,160,96,260] 13 (by decide) (choices 1) [1,2,4,64] r29982 c29982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u11564
  · exact u11565
  · exact u11566
  · exact u11567

def r29983 : Route 9 := (fun mask => (mask,id))

def c29983 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29983 : Upper (D 6) (R 6) [10,17,160,96,320] 13 := by
  apply FastRouting.sound _ _ [10,17,160,96,320] 13 (by decide) (choices 1) [1,2,4] r29983 c29983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11568
  · exact u11569
  · exact u11570

def b29984 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 388 11 52 100 100 228 356), lower := (rows 11 19 388 11 52 32 64 128 256), losses := [] }

theorem u29984 : Upper (D 6) (R 6) [10,17,384,3,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29984
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29985 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 11, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 388 11 112 100 100 228 356), lower := (rows 11 19 388 11 112 32 64 128 256), losses := [] }

theorem u29985 : Upper (D 6) (R 6) [10,17,384,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29985
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29986 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 27, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 388 13 22 96 96 224 352), lower := (rows 11 19 388 13 22 32 64 128 256), losses := [] }

theorem u29986 : Upper (D 6) (R 6) [10,17,384,5,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29986
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29987 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 388 13 50 100 100 228 356), lower := (rows 11 19 388 13 50 32 64 128 256), losses := [] }

theorem u29987 : Upper (D 6) (R 6) [10,17,384,5,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29987
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29988 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 388 13 52 98 98 226 354), lower := (rows 11 19 388 13 52 32 64 128 256), losses := [] }

theorem u29988 : Upper (D 6) (R 6) [10,17,384,5,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29988
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29989 : Route 9 := (fun mask => (mask,id))

def c29989 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29989 : Upper (D 6) (R 6) [10,17,384,5,96] 13 := by
  apply FastRouting.sound _ _ [10,17,384,5,96] 13 (by decide) (choices 1) [2,4,64] r29989 c29989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11571
  · exact u11572
  · exact u11573

def b29990 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 11, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 388 14 52 97 97 225 353), lower := (rows 11 19 388 14 52 32 64 128 256), losses := [] }

theorem u29990 : Upper (D 6) (R 6) [10,17,384,6,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29990
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29991 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 388 14 112 101 101 229 357), lower := (rows 11 19 388 14 112 32 64 128 256), losses := [] }

theorem u29991 : Upper (D 6) (R 6) [10,17,384,6,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29991
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29992 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 27, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 388 41 50 100 68 196 324), lower := (rows 11 19 388 41 50 32 64 128 256), losses := [] }

theorem u29992 : Upper (D 6) (R 6) [10,17,384,33,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29992
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29993 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 388 41 52 102 70 198 326), lower := (rows 11 19 388 41 52 32 64 128 256), losses := [] }

theorem u29993 : Upper (D 6) (R 6) [10,17,384,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29993
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29994 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 388 41 82 100 100 228 356), lower := (rows 11 19 388 41 82 32 64 128 256), losses := [] }

theorem u29994 : Upper (D 6) (R 6) [10,17,384,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29994
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r29995 : Route 9 := (fun mask => (mask,id))

def c29995 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29995 : Upper (D 6) (R 6) [10,17,384,33,68] 13 := by
  apply FastRouting.sound _ _ [10,17,384,33,68] 13 (by decide) (choices 1) [2,4,64] r29995 c29995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11574
  · exact u11575
  · exact u11576

def b29996 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 388 41 112 102 70 198 326), lower := (rows 11 19 388 41 112 32 64 128 256), losses := [] }

theorem u29996 : Upper (D 6) (R 6) [10,17,384,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29996
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29997 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 388 42 52 101 69 197 325), lower := (rows 11 19 388 42 52 32 64 128 256), losses := [] }

theorem u29997 : Upper (D 6) (R 6) [10,17,384,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29997
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29998 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 1, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 19 388 42 84 101 101 229 357), lower := (rows 11 19 388 42 84 32 64 128 256), losses := [] }

theorem u29998 : Upper (D 6) (R 6) [10,17,384,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29998
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b29999 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 11, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 19 388 42 112 101 69 197 325), lower := (rows 11 19 388 42 112 32 64 128 256), losses := [] }

theorem u29999 : Upper (D 6) (R 6) [10,17,384,34,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b29999
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u29999
end Delivery.IrregularNine14.P06
