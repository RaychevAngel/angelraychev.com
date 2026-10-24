import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0034
import IrregularNine14P08C0035

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8940 : Route 9 := (fun mask => (mask,id))

def c8940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8940 : Upper (D 8) (R 8) [34,68,40,257,96] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,96] 13 (by decide) (choices 1) [1,16,128] r8940 c8940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2069
  · exact u2070
  · exact u2071

def r8941 : Route 9 := (fun mask => (mask,id))

def c8941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8941 : Upper (D 8) (R 8) [34,68,40,257,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,129] 13 (by decide) (choices 1) [16,64,128] r8941 c8941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2072
  · exact u2073
  · exact u2074

def r8942 : Route 9 := (fun mask => (mask,id))

def c8942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8942 : Upper (D 8) (R 8) [34,68,40,257,160] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,160] 13 (by decide) (choices 1) [1,16,64,128] r8942 c8942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2075
  · exact u2076
  · exact u2077
  · exact u2078

def r8943 : Route 9 := (fun mask => (mask,id))

def c8943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8943 : Upper (D 8) (R 8) [34,68,40,257,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,257,192] 13 (by decide) (choices 1) [1,16,128] r8943 c8943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2079
  · exact u2080
  · exact u2081

def b8944 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 44 280 49 225 193 193 449), lower := (rows 35 70 44 280 49 32 64 128 256), losses := [] }

theorem u8944 : Upper (D 8) (R 8) [34,68,40,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8945 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 280 81 161 225 161 417), lower := (rows 35 70 44 280 81 32 64 128 256), losses := [] }

theorem u8945 : Upper (D 8) (R 8) [34,68,40,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8946 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 280 112 161 193 129 385), lower := (rows 35 70 44 280 112 32 64 128 256), losses := [] }

theorem u8946 : Upper (D 8) (R 8) [34,68,40,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8947 : Route 9 := (fun mask => (mask,id))

def c8947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8947 : Upper (D 8) (R 8) [34,68,40,272,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,272,129] 13 (by decide) (choices 1) [1,64,128] r8947 c8947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2082
  · exact u2083
  · exact u2084

def r8948 : Route 9 := (fun mask => (mask,id))

def c8948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8948 : Upper (D 8) (R 8) [34,68,40,272,160] 13 := by
  apply FastRouting.sound _ _ [34,68,40,272,160] 13 (by decide) (choices 1) [1,64,128] r8948 c8948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2085
  · exact u2086
  · exact u2087

def b8949 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 280 208 161 225 161 417), lower := (rows 35 70 44 280 208 32 64 128 256), losses := [] }

theorem u8949 : Upper (D 8) (R 8) [34,68,40,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8950 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 44 392 49 241 209 209 465), lower := (rows 35 70 44 392 49 32 64 128 256), losses := [] }

theorem u8950 : Upper (D 8) (R 8) [34,68,40,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8951 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 392 81 177 241 177 433), lower := (rows 35 70 44 392 81 32 64 128 256), losses := [] }

theorem u8951 : Upper (D 8) (R 8) [34,68,40,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8952 : Route 9 := (fun mask => (mask,id))

def c8952 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8952 : Upper (D 8) (R 8) [34,68,40,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,96] 13 (by decide) (choices 1) [1,16,128] r8952 c8952
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2088
  · exact u2089
  · exact u2090

def r8953 : Route 9 := (fun mask => (mask,id))

def c8953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8953 : Upper (D 8) (R 8) [34,68,40,384,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,129] 13 (by decide) (choices 1) [1,16,64] r8953 c8953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2091
  · exact u2092
  · exact u2093

def r8954 : Route 9 := (fun mask => (mask,id))

def c8954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8954 : Upper (D 8) (R 8) [34,68,40,384,160] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,160] 13 (by decide) (choices 1) [1,16,64] r8954 c8954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2094
  · exact u2095
  · exact u2096

def r8955 : Route 9 := (fun mask => (mask,id))

def c8955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8955 : Upper (D 8) (R 8) [34,68,40,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,192] 13 (by decide) (choices 1) [1,16] r8955 c8955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2097
  · exact u2098

def b8956 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 25 56 480 480 480 480), lower := (rows 35 70 133 25 56 32 64 128 256), losses := [] }

theorem u8956 : Upper (D 8) (R 8) [34,68,129,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8957 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 25 88 416 480 416 416), lower := (rows 35 70 133 25 88 32 64 128 256), losses := [] }

theorem u8957 : Upper (D 8) (R 8) [34,68,129,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8958 : PairBound 9 := { available := 424, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 133 25 112 424 488 424 424), lower := (rows 35 70 133 25 112 32 64 128 256), losses := [] }

theorem u8958 : Upper (D 8) (R 8) [34,68,129,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8959 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 25 152 352 352 480 352), lower := (rows 35 70 133 25 152 32 64 128 256), losses := [] }

theorem u8959 : Upper (D 8) (R 8) [34,68,129,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8960 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 133 25 176 360 360 488 360), lower := (rows 35 70 133 25 176 32 64 128 256), losses := [] }

theorem u8960 : Upper (D 8) (R 8) [34,68,129,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8960 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8961 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 133 25 208 296 360 424 296), lower := (rows 35 70 133 25 208 32 64 128 256), losses := [] }

theorem u8961 : Upper (D 8) (R 8) [34,68,129,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8961 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8962 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 133 25 280 224 224 224 480), lower := (rows 35 70 133 25 280 32 64 128 256), losses := [] }

theorem u8962 : Upper (D 8) (R 8) [34,68,129,17,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8962 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8963 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 133 25 304 232 232 232 488), lower := (rows 35 70 133 25 304 32 64 128 256), losses := [] }

theorem u8963 : Upper (D 8) (R 8) [34,68,129,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8963 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8964 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 133 25 336 168 232 168 424), lower := (rows 35 70 133 25 336 32 64 128 256), losses := [] }

theorem u8964 : Upper (D 8) (R 8) [34,68,129,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8964 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8965 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 133 25 400 104 104 232 360), lower := (rows 35 70 133 25 400 32 64 128 256), losses := [] }

theorem u8965 : Upper (D 8) (R 8) [34,68,129,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8965 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8966 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 41 56 496 464 464 464), lower := (rows 35 70 133 41 56 32 64 128 256), losses := [] }

theorem u8966 : Upper (D 8) (R 8) [34,68,129,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8966 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8967 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 41 88 432 496 432 432), lower := (rows 35 70 133 41 88 32 64 128 256), losses := [] }

theorem u8967 : Upper (D 8) (R 8) [34,68,129,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8967 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8968 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 41 112 440 472 408 408), lower := (rows 35 70 133 41 112 32 64 128 256), losses := [] }

theorem u8968 : Upper (D 8) (R 8) [34,68,129,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8968 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8969 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 41 152 368 368 496 368), lower := (rows 35 70 133 41 152 32 64 128 256), losses := [] }

theorem u8969 : Upper (D 8) (R 8) [34,68,129,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8969 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8970 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 41 176 376 344 472 344), lower := (rows 35 70 133 41 176 32 64 128 256), losses := [] }

theorem u8970 : Upper (D 8) (R 8) [34,68,129,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8970 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8971 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 41 208 312 376 440 312), lower := (rows 35 70 133 41 208 32 64 128 256), losses := [] }

theorem u8971 : Upper (D 8) (R 8) [34,68,129,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8971 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8972 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 41 280 240 240 240 496), lower := (rows 35 70 133 41 280 32 64 128 256), losses := [] }

theorem u8972 : Upper (D 8) (R 8) [34,68,129,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8972 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8973 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 41 304 248 216 216 472), lower := (rows 35 70 133 41 304 32 64 128 256), losses := [] }

theorem u8973 : Upper (D 8) (R 8) [34,68,129,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8973 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8974 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 41 336 184 248 184 440), lower := (rows 35 70 133 41 336 32 64 128 256), losses := [] }

theorem u8974 : Upper (D 8) (R 8) [34,68,129,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8974 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8975 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 41 400 120 120 248 376), lower := (rows 35 70 133 41 400 32 64 128 256), losses := [] }

theorem u8975 : Upper (D 8) (R 8) [34,68,129,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8975 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8976 : PairBound 9 := { available := 449, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 56 56 481 449 449 449), lower := (rows 35 70 133 56 56 32 64 128 256), losses := [] }

theorem u8976 : Upper (D 8) (R 8) [34,68,129,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8976 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8977 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 56 81 424 488 424 424), lower := (rows 35 70 133 56 81 32 64 128 256), losses := [] }

theorem u8977 : Upper (D 8) (R 8) [34,68,129,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8977 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8978 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 56 88 417 481 417 417), lower := (rows 35 70 133 56 88 32 64 128 256), losses := [] }

theorem u8978 : Upper (D 8) (R 8) [34,68,129,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8978 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8979 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 56 112 425 457 393 393), lower := (rows 35 70 133 56 112 32 64 128 256), losses := [] }

theorem u8979 : Upper (D 8) (R 8) [34,68,129,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8979 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8980 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 133 56 145 360 360 488 360), lower := (rows 35 70 133 56 145 32 64 128 256), losses := [] }

theorem u8980 : Upper (D 8) (R 8) [34,68,129,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8980 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8981 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 133 56 152 353 353 481 353), lower := (rows 35 70 133 56 152 32 64 128 256), losses := [] }

theorem u8981 : Upper (D 8) (R 8) [34,68,129,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8981 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8982 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 56 176 361 329 457 329), lower := (rows 35 70 133 56 176 32 64 128 256), losses := [] }

theorem u8982 : Upper (D 8) (R 8) [34,68,129,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8982 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8983 : Route 9 := (fun mask => (mask,id))

def c8983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8983 : Upper (D 8) (R 8) [34,68,129,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,192] 13 (by decide) (choices 1) [1,8,256] r8983 c8983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2099
  · exact u2100
  · exact u2101

def b8984 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 56 273 232 232 232 488), lower := (rows 35 70 133 56 273 32 64 128 256), losses := [] }

theorem u8984 : Upper (D 8) (R 8) [34,68,129,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8984 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8985 : Route 9 := (fun mask => (mask,id))

def c8985 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8985 : Upper (D 8) (R 8) [34,68,129,48,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,264] 13 (by decide) (choices 1) [1,64,128] r8985 c8985
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2102
  · exact u2103
  · exact u2104

def b8986 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 56 304 233 201 201 457), lower := (rows 35 70 133 56 304 32 64 128 256), losses := [] }

theorem u8986 : Upper (D 8) (R 8) [34,68,129,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8986 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8987 : Route 9 := (fun mask => (mask,id))

def c8987 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8987 : Upper (D 8) (R 8) [34,68,129,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,320] 13 (by decide) (choices 1) [1,8,128] r8987 c8987
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2105
  · exact u2106
  · exact u2107

def r8988 : Route 9 := (fun mask => (mask,id))

def c8988 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8988 : Upper (D 8) (R 8) [34,68,129,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,384] 13 (by decide) (choices 1) [1,8,64] r8988 c8988
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2108
  · exact u2109
  · exact u2110

def b8989 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 152 304 368 432 304), lower := (rows 35 70 133 73 152 32 64 128 256), losses := [] }

theorem u8989 : Upper (D 8) (R 8) [34,68,129,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8989 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8990 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 176 312 376 440 312), lower := (rows 35 70 133 73 176 32 64 128 256), losses := [] }

theorem u8990 : Upper (D 8) (R 8) [34,68,129,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8990 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8991 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 280 176 240 176 432), lower := (rows 35 70 133 73 280 32 64 128 256), losses := [] }

theorem u8991 : Upper (D 8) (R 8) [34,68,129,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8991 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8992 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 304 184 248 184 440), lower := (rows 35 70 133 73 304 32 64 128 256), losses := [] }

theorem u8992 : Upper (D 8) (R 8) [34,68,129,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8992 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8993 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 400 56 120 184 312), lower := (rows 35 70 133 73 400 32 64 128 256), losses := [] }

theorem u8993 : Upper (D 8) (R 8) [34,68,129,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8993 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8994 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 133 88 145 296 360 424 296), lower := (rows 35 70 133 88 145 32 64 128 256), losses := [] }

theorem u8994 : Upper (D 8) (R 8) [34,68,129,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8994 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8995 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 88 152 289 353 417 289), lower := (rows 35 70 133 88 152 32 64 128 256), losses := [] }

theorem u8995 : Upper (D 8) (R 8) [34,68,129,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8995 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8996 : Route 9 := (fun mask => (mask,id))

def c8996 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8996 : Upper (D 8) (R 8) [34,68,129,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,160] 13 (by decide) (choices 1) [1,8,256] r8996 c8996
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2111
  · exact u2112
  · exact u2113

def b8997 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 133 88 273 168 232 168 424), lower := (rows 35 70 133 88 273 32 64 128 256), losses := [] }

theorem u8997 : Upper (D 8) (R 8) [34,68,129,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8997 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8998 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 88 280 161 225 161 417), lower := (rows 35 70 133 88 280 32 64 128 256), losses := [] }

theorem u8998 : Upper (D 8) (R 8) [34,68,129,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8998 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8999 : Route 9 := (fun mask => (mask,id))

def c8999 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8999 : Upper (D 8) (R 8) [34,68,129,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,288] 13 (by decide) (choices 1) [1,8,128] r8999 c8999
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2114
  · exact u2115
  · exact u2116

#print axioms u8999
end Delivery.IrregularNine14.P08
