import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0012

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8940 : Route 9 := (fun mask => (mask,id))

def c8940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8940 : Upper (D 6) (R 6) [6,9,96,144,288,2] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,288,2] 13 (by decide) (choices 1) [1,4] r8940 c8940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u731
  · exact u732

def r8941 : Route 9 := (fun mask => (mask,id))

def c8941 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8941 : Upper (D 6) (R 6) [6,9,96,144,288,4] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,288,4] 13 (by decide) (choices 1) [1,2] r8941 c8941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u733
  · exact u734

def b8942 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 152 304 96 71 135 263), lower := (rows 7 11 100 152 304 96 64 128 256), losses := [] }

theorem u8942 : Upper (D 6) (R 6) [6,9,96,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8943 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 336, targets := 34 }], pairs := [(2,0),(4,1),(4,5)], upper := (rows 7 11 100 168 81 34 340 404 276), lower := (rows 7 11 100 168 81 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 42 100 168 508 34 64 128 256) }] }

theorem u8943 : Upper (D 6) (R 6) [6,9,96,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8944 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 11 100 168 81 36 338 402 274), lower := (rows 7 11 100 168 81 36 64 128 256), losses := [] }

theorem u8944 : Upper (D 6) (R 6) [6,9,96,160,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8945 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 100 168 81 48 326 390 262), lower := (rows 7 11 100 168 81 48 64 128 256), losses := [] }

theorem u8945 : Upper (D 6) (R 6) [6,9,96,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8945 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8946 : Route 9 := (fun mask => (mask,id))

def c8946 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8946 : Upper (D 6) (R 6) [6,9,96,160,65,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,65,256] 13 (by decide) (choices 1) [2,4,16] r8946 c8946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u735
  · exact u736
  · exact u737

def b8947 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 336, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 100 168 82 33 340 404 276), lower := (rows 7 11 100 168 82 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 19 32 99 163 291), good := (rows 478 478 492 492 466 508 64 128 256) }] }

theorem u8947 : Upper (D 6) (R 6) [6,9,96,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8948 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 11 100 168 82 36 337 401 273), lower := (rows 7 11 100 168 82 36 64 128 256), losses := [] }

theorem u8948 : Upper (D 6) (R 6) [6,9,96,160,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8949 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 100 168 82 48 325 389 261), lower := (rows 7 11 100 168 82 48 64 128 256), losses := [] }

theorem u8949 : Upper (D 6) (R 6) [6,9,96,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8949 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8950 : Route 9 := (fun mask => (mask,id))

def c8950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8950 : Upper (D 6) (R 6) [6,9,96,160,66,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,66,256] 13 (by decide) (choices 1) [1,4,16] r8950 c8950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u738
  · exact u739
  · exact u740

def b8951 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 336, targets := 34 }], pairs := [(2,0),(4,1),(4,5)], upper := (rows 7 11 100 168 273 34 84 212 340), lower := (rows 7 11 100 168 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 42 100 168 508 34 64 128 256) }] }

theorem u8951 : Upper (D 6) (R 6) [6,9,96,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8952 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 11 100 168 273 36 82 210 338), lower := (rows 7 11 100 168 273 36 64 128 256), losses := [] }

theorem u8952 : Upper (D 6) (R 6) [6,9,96,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8953 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(4,5)], upper := (rows 7 11 100 168 273 48 70 198 326), lower := (rows 7 11 100 168 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 48 65 129 257), good := (rows 454 458 100 168 508 60 64 128 256) }] }

theorem u8953 : Upper (D 6) (R 6) [6,9,96,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8953 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8954 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 168 273 96 86 150 278), lower := (rows 7 11 100 168 273 96 64 128 256), losses := [] }

theorem u8954 : Upper (D 6) (R 6) [6,9,96,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8955 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 336, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 100 168 274 33 84 212 340), lower := (rows 7 11 100 168 274 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 44 44 19 32 99 163 291), good := (rows 478 478 492 492 466 508 64 128 256) }] }

theorem u8955 : Upper (D 6) (R 6) [6,9,96,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8956 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 11 100 168 274 36 81 209 337), lower := (rows 7 11 100 168 274 36 64 128 256), losses := [] }

theorem u8956 : Upper (D 6) (R 6) [6,9,96,160,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8957 : Route 9 := (fun mask => (mask,id))

def c8957 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8957 : Upper (D 6) (R 6) [6,9,96,160,258,16] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,258,16] 13 (by decide) (choices 1) [1,4] r8957 c8957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u741
  · exact u742

def b8958 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 168 274 96 85 149 277), lower := (rows 7 11 100 168 274 96 64 128 256), losses := [] }

theorem u8958 : Upper (D 6) (R 6) [6,9,96,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8959 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 336, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 100 168 276 33 82 210 338), lower := (rows 7 11 100 168 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 49 32 67 131 259), good := (rows 470 474 124 188 276 508 64 128 256) }] }

theorem u8959 : Upper (D 6) (R 6) [6,9,96,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8960 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 34 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 11 100 168 276 34 81 209 337), lower := (rows 7 11 100 168 276 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 36 40 49 32 67 131 259), good := (rows 469 473 124 188 276 508 64 128 256) }] }

theorem u8960 : Upper (D 6) (R 6) [6,9,96,160,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8960 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8961 : Route 9 := (fun mask => (mask,id))

def c8961 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8961 : Upper (D 6) (R 6) [6,9,96,160,260,16] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,260,16] 13 (by decide) (choices 1) [1,2] r8961 c8961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u743
  · exact u744

def b8962 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 168 276 96 83 147 275), lower := (rows 7 11 100 168 276 96 64 128 256), losses := [] }

theorem u8962 : Upper (D 6) (R 6) [6,9,96,160,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8963 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 336, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 100 168 336 33 86 150 278), lower := (rows 7 11 100 168 336 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 51 32 65 129 257), good := (rows 470 474 124 188 336 508 64 128 256) }] }

theorem u8963 : Upper (D 6) (R 6) [6,9,96,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8964 : Route 9 := (fun mask => (mask,id))

def c8964 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8964 : Upper (D 6) (R 6) [6,9,96,160,320,2] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,320,2] 13 (by decide) (choices 1) [1,4,16] r8964 c8964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u745
  · exact u746
  · exact u747

def b8965 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 11 100 168 336 36 83 147 275), lower := (rows 7 11 100 168 336 36 64 128 256), losses := [] }

theorem u8965 : Upper (D 6) (R 6) [6,9,96,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8966 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 100 168 336 48 71 135 263), lower := (rows 7 11 100 168 336 48 64 128 256), losses := [] }

theorem u8966 : Upper (D 6) (R 6) [6,9,96,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8966 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8967 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 100 392 49 34 84 212 340), lower := (rows 7 11 100 392 49 34 64 128 256), losses := [] }

theorem u8967 : Upper (D 6) (R 6) [6,9,96,384,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8968 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 7 11 100 392 49 36 82 210 338), lower := (rows 7 11 100 392 49 36 64 128 256), losses := [] }

theorem u8968 : Upper (D 6) (R 6) [6,9,96,384,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8968 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8969 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 11 100 392 49 48 70 198 326), lower := (rows 7 11 100 392 49 48 64 128 256), losses := [] }

theorem u8969 : Upper (D 6) (R 6) [6,9,96,384,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8969 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8970 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 392 49 96 86 150 278), lower := (rows 7 11 100 392 49 96 64 128 256), losses := [] }

theorem u8970 : Upper (D 6) (R 6) [6,9,96,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8971 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 100 392 50 33 84 212 340), lower := (rows 7 11 100 392 50 33 64 128 256), losses := [] }

theorem u8971 : Upper (D 6) (R 6) [6,9,96,384,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8972 : PairBound 9 := { available := 81, camps := [{ cop := 6, region := 36, targets := 3 },{ cop := 0, region := 48, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 100 392 50 36 81 209 337), lower := (rows 7 11 100 392 50 36 64 128 256), losses := [] }

theorem u8972 : Upper (D 6) (R 6) [6,9,96,384,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8972 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8973 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 100 392 50 48 69 197 325), lower := (rows 7 11 100 392 50 48 64 128 256), losses := [] }

theorem u8973 : Upper (D 6) (R 6) [6,9,96,384,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8973 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8974 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 100 392 50 96 85 149 277), lower := (rows 7 11 100 392 50 96 64 128 256), losses := [] }

theorem u8974 : Upper (D 6) (R 6) [6,9,96,384,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8975 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 133 56 84 34 352 480 352), lower := (rows 7 11 133 56 84 34 64 128 256), losses := [] }

theorem u8975 : Upper (D 6) (R 6) [6,9,129,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8976 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 133 56 84 96 354 418 290), lower := (rows 7 11 133 56 84 96 64 128 256), losses := [] }

theorem u8976 : Upper (D 6) (R 6) [6,9,129,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8977 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 133 56 84 288 98 226 354), lower := (rows 7 11 133 56 84 288 64 128 256), losses := [] }

theorem u8977 : Upper (D 6) (R 6) [6,9,129,48,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8977 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8978 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 133 56 276 34 96 224 352), lower := (rows 7 11 133 56 276 34 64 128 256), losses := [] }

theorem u8978 : Upper (D 6) (R 6) [6,9,129,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8979 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 11 133 56 276 96 98 226 354), lower := (rows 7 11 133 56 276 96 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 103 67 131 259), good := (rows 483 491 481 56 312 96 96 128 256) }] }

theorem u8979 : Upper (D 6) (R 6) [6,9,129,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8980 : Route 9 := (fun mask => (mask,id))

def c8980 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8980 : Upper (D 6) (R 6) [6,9,129,48,320,2] 13 := by
  apply FastRouting.sound _ _ [6,9,129,48,320,2] 13 (by decide) (choices 1) [4,32] r8980 c8980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u748
  · exact u749

def r8981 : Route 9 := (fun mask => (mask,id))

def c8981 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8981 : Upper (D 6) (R 6) [6,9,129,48,320,4] 13 := by
  apply FastRouting.sound _ _ [6,9,129,48,320,4] 13 (by decide) (choices 1) [2,32] r8981 c8981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u750
  · exact u751

def b8982 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 133 56 336 96 102 166 294), lower := (rows 7 11 133 56 336 96 64 128 256), losses := [] }

theorem u8982 : Upper (D 6) (R 6) [6,9,129,48,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8983 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 328, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 104 52 34 336 464 336), lower := (rows 7 11 133 104 52 34 64 128 256), losses := [] }

theorem u8983 : Upper (D 6) (R 6) [6,9,129,96,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8983 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8984 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 133 104 52 48 322 450 322), lower := (rows 7 11 133 104 52 48 64 128 256), losses := [] }

theorem u8984 : Upper (D 6) (R 6) [6,9,129,96,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8984 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8985 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 133 104 52 96 338 402 274), lower := (rows 7 11 133 104 52 96 64 128 256), losses := [] }

theorem u8985 : Upper (D 6) (R 6) [6,9,129,96,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8986 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 133 104 52 288 82 210 338), lower := (rows 7 11 133 104 52 288 64 128 256), losses := [] }

theorem u8986 : Upper (D 6) (R 6) [6,9,129,96,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8986 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8987 : Route 9 := (fun mask => (mask,id))

def c8987 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8987 : Upper (D 6) (R 6) [6,9,129,96,258,4] 13 := by
  apply FastRouting.sound _ _ [6,9,129,96,258,4] 13 (by decide) (choices 1) [16,32] r8987 c8987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u752
  · exact u753

def b8988 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 133 104 274 48 100 228 356), lower := (rows 7 11 133 104 274 48 64 128 256), losses := [] }

theorem u8988 : Upper (D 6) (R 6) [6,9,129,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8988 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8989 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 133 104 274 96 116 180 308), lower := (rows 7 11 133 104 274 96 64 128 256), losses := [] }

theorem u8989 : Upper (D 6) (R 6) [6,9,129,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8990 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 133 104 276 34 112 240 368), lower := (rows 7 11 133 104 276 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 6 40 50 32 104 168 296), good := (rows 21 477 133 504 276 508 64 128 256) }] }

theorem u8990 : Upper (D 6) (R 6) [6,9,129,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8990 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8991 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 11 133 104 276 48 98 226 354), lower := (rows 7 11 133 104 276 48 64 128 256), losses := [] }

theorem u8991 : Upper (D 6) (R 6) [6,9,129,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8991 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8992 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 133 104 276 96 114 178 306), lower := (rows 7 11 133 104 276 96 64 128 256), losses := [] }

theorem u8992 : Upper (D 6) (R 6) [6,9,129,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8993 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 376, targets := 1 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 133 104 304 34 84 212 340), lower := (rows 7 11 133 104 304 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 56 56 32 98 162 290), good := (rows 453 477 133 504 504 508 64 128 256) }] }

theorem u8993 : Upper (D 6) (R 6) [6,9,129,96,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8994 : Route 9 := (fun mask => (mask,id))

def c8994 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8994 : Upper (D 6) (R 6) [6,9,129,96,288,4] 13 := by
  apply FastRouting.sound _ _ [6,9,129,96,288,4] 13 (by decide) (choices 1) [2,16] r8994 c8994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u754
  · exact u755

def b8995 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 133 104 304 48 70 198 326), lower := (rows 7 11 133 104 304 48 64 128 256), losses := [] }

theorem u8995 : Upper (D 6) (R 6) [6,9,129,96,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8995 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8996 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 133 104 304 96 86 150 278), lower := (rows 7 11 133 104 304 96 64 128 256), losses := [] }

theorem u8996 : Upper (D 6) (R 6) [6,9,129,96,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8997 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 328, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 7 11 133 280 52 34 96 224 352), lower := (rows 7 11 133 280 52 34 64 128 256), losses := [] }

theorem u8997 : Upper (D 6) (R 6) [6,9,129,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8998 : Route 9 := (fun mask => (mask,id))

def c8998 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8998 : Upper (D 6) (R 6) [6,9,129,272,36,64] 13 := by
  apply FastRouting.sound _ _ [6,9,129,272,36,64] 13 (by decide) (choices 1) [2,32] r8998 c8998
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u756
  · exact u757

def r8999 : Route 9 := (fun mask => (mask,id))

def c8999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8999 : Upper (D 6) (R 6) [6,9,129,272,96,2] 13 := by
  apply FastRouting.sound _ _ [6,9,129,272,96,2] 13 (by decide) (choices 1) [4,32] r8999 c8999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u758
  · exact u759

#print axioms u8999
end Delivery.IrregularNine14.P06
