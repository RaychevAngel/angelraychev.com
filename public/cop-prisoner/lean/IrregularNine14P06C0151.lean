import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0013
import IrregularNine14P06C0014

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9060 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 148 296 112 96 71 135 263), lower := (rows 7 11 148 296 112 96 64 128 256), losses := [] }

theorem u9060 : Upper (D 6) (R 6) [6,9,144,288,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9061 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 26 112 33 324 452 324), lower := (rows 7 11 164 26 112 33 64 128 256), losses := [] }

theorem u9061 : Upper (D 6) (R 6) [6,9,160,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9062 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 26 112 36 321 449 321), lower := (rows 7 11 164 26 112 36 64 128 256), losses := [] }

theorem u9062 : Upper (D 6) (R 6) [6,9,160,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9063 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 26 112 96 325 389 261), lower := (rows 7 11 164 26 112 96 64 128 256), losses := [] }

theorem u9063 : Upper (D 6) (R 6) [6,9,160,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9064 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 11 164 26 112 288 69 197 325), lower := (rows 7 11 164 26 112 288 64 128 256), losses := [] }

theorem u9064 : Upper (D 6) (R 6) [6,9,160,18,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9064 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9065 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 26 304 33 68 196 324), lower := (rows 7 11 164 26 304 33 64 128 256), losses := [] }

theorem u9065 : Upper (D 6) (R 6) [6,9,160,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9066 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 26 304 36 65 193 321), lower := (rows 7 11 164 26 304 36 64 128 256), losses := [] }

theorem u9066 : Upper (D 6) (R 6) [6,9,160,18,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9067 : Route 9 := (fun mask => (mask,id))

def c9067 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9067 : Upper (D 6) (R 6) [6,9,160,18,288,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,18,288,64] 13 (by decide) (choices 1) [1,4] r9067 c9067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u817
  · exact u818

def b9068 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 26 336 33 100 228 356), lower := (rows 7 11 164 26 336 33 64 128 256), losses := [] }

theorem u9068 : Upper (D 6) (R 6) [6,9,160,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9069 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 26 336 36 97 225 353), lower := (rows 7 11 164 26 336 36 64 128 256), losses := [] }

theorem u9069 : Upper (D 6) (R 6) [6,9,160,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9070 : Route 9 := (fun mask => (mask,id))

def c9070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9070 : Upper (D 6) (R 6) [6,9,160,18,320,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,18,320,64] 13 (by decide) (choices 1) [1,4,32] r9070 c9070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u819
  · exact u820
  · exact u821

def b9071 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 56 84 33 322 450 322), lower := (rows 7 11 164 56 84 33 64 128 256), losses := [] }

theorem u9071 : Upper (D 6) (R 6) [6,9,160,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9072 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 56 84 34 321 449 321), lower := (rows 7 11 164 56 84 34 64 128 256), losses := [] }

theorem u9072 : Upper (D 6) (R 6) [6,9,160,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9073 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 56 84 96 323 387 259), lower := (rows 7 11 164 56 84 96 64 128 256), losses := [] }

theorem u9073 : Upper (D 6) (R 6) [6,9,160,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9074 : Route 9 := (fun mask => (mask,id))

def c9074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9074 : Upper (D 6) (R 6) [6,9,160,48,68,256] 13 := by
  apply FastRouting.sound _ _ [6,9,160,48,68,256] 13 (by decide) (choices 1) [1,2] r9074 c9074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u822
  · exact u823

def b9075 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 56 276 33 66 194 322), lower := (rows 7 11 164 56 276 33 64 128 256), losses := [] }

theorem u9075 : Upper (D 6) (R 6) [6,9,160,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9076 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 11 164 56 276 34 65 193 321), lower := (rows 7 11 164 56 276 34 64 128 256), losses := [] }

theorem u9076 : Upper (D 6) (R 6) [6,9,160,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9077 : Route 9 := (fun mask => (mask,id))

def c9077 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9077 : Upper (D 6) (R 6) [6,9,160,48,260,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,48,260,64] 13 (by decide) (choices 1) [1,2] r9077 c9077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u824
  · exact u825

def b9078 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 336, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 164 56 336 33 70 198 326), lower := (rows 7 11 164 56 336 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 51 32 65 129 257), good := (rows 478 474 188 60 336 508 64 128 256) }] }

theorem u9078 : Upper (D 6) (R 6) [6,9,160,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9079 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 336, targets := 34 }], pairs := [(3,1),(4,1),(4,5)], upper := (rows 7 11 164 56 336 34 69 197 325), lower := (rows 7 11 164 56 336 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 40 19 32 65 129 257), good := (rows 469 473 172 56 336 56 64 128 256) }] }

theorem u9079 : Upper (D 6) (R 6) [6,9,160,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9080 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 56 336 36 67 195 323), lower := (rows 7 11 164 56 336 36 64 128 256), losses := [] }

theorem u9080 : Upper (D 6) (R 6) [6,9,160,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9081 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 164 56 336 96 71 135 263), lower := (rows 7 11 164 56 336 96 64 128 256), losses := [] }

theorem u9081 : Upper (D 6) (R 6) [6,9,160,48,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9082 : PairBound 9 := { available := 276, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 74 112 33 340 404 276), lower := (rows 7 11 164 74 112 33 64 128 256), losses := [] }

theorem u9082 : Upper (D 6) (R 6) [6,9,160,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9083 : PairBound 9 := { available := 273, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 74 112 36 337 401 273), lower := (rows 7 11 164 74 112 36 64 128 256), losses := [] }

theorem u9083 : Upper (D 6) (R 6) [6,9,160,66,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9084 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 331, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 164 74 112 48 325 389 261), lower := (rows 7 11 164 74 112 48 64 128 256), losses := [] }

theorem u9084 : Upper (D 6) (R 6) [6,9,160,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9084 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9085 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 11 164 74 112 288 85 149 277), lower := (rows 7 11 164 74 112 288 64 128 256), losses := [] }

theorem u9085 : Upper (D 6) (R 6) [6,9,160,66,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9085 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9086 : PairBound 9 := { available := 112, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 74 276 33 112 240 368), lower := (rows 7 11 164 74 276 33 64 128 256), losses := [] }

theorem u9086 : Upper (D 6) (R 6) [6,9,160,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9087 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 11 164 74 276 48 97 225 353), lower := (rows 7 11 164 74 276 48 64 128 256), losses := [] }

theorem u9087 : Upper (D 6) (R 6) [6,9,160,66,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9087 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9088 : Route 9 := (fun mask => (mask,id))

def c9088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9088 : Upper (D 6) (R 6) [6,9,160,66,260,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,66,260,64] 13 (by decide) (choices 1) [1,16,32] r9088 c9088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u826
  · exact u827
  · exact u828

def b9089 : PairBound 9 := { available := 84, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 74 304 33 84 212 340), lower := (rows 7 11 164 74 304 33 64 128 256), losses := [] }

theorem u9089 : Upper (D 6) (R 6) [6,9,160,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9090 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 74 304 36 81 209 337), lower := (rows 7 11 164 74 304 36 64 128 256), losses := [] }

theorem u9090 : Upper (D 6) (R 6) [6,9,160,66,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9091 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 164 74 304 48 69 197 325), lower := (rows 7 11 164 74 304 48 64 128 256), losses := [] }

theorem u9091 : Upper (D 6) (R 6) [6,9,160,66,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9091 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9092 : Route 9 := (fun mask => (mask,id))

def c9092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9092 : Upper (D 6) (R 6) [6,9,160,66,288,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,66,288,64] 13 (by decide) (choices 1) [1,4,16] r9092 c9092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u829
  · exact u830
  · exact u831

def b9093 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 164 74 336 33 116 180 308), lower := (rows 7 11 164 74 336 33 64 128 256), losses := [] }

theorem u9093 : Upper (D 6) (R 6) [6,9,160,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9094 : PairBound 9 := { available := 49, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 74 336 36 113 177 305), lower := (rows 7 11 164 74 336 36 64 128 256), losses := [] }

theorem u9094 : Upper (D 6) (R 6) [6,9,160,66,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9095 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 11 164 74 336 48 101 165 293), lower := (rows 7 11 164 74 336 48 64 128 256), losses := [] }

theorem u9095 : Upper (D 6) (R 6) [6,9,160,66,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9095 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9096 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 88 50 33 324 452 324), lower := (rows 7 11 164 88 50 33 64 128 256), losses := [] }

theorem u9096 : Upper (D 6) (R 6) [6,9,160,80,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9097 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 88 50 36 321 449 321), lower := (rows 7 11 164 88 50 36 64 128 256), losses := [] }

theorem u9097 : Upper (D 6) (R 6) [6,9,160,80,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9098 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 389, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(2,1),(2,6)], upper := (rows 7 11 164 88 50 96 325 389 261), lower := (rows 7 11 164 88 50 96 64 128 256), losses := [] }

theorem u9098 : Upper (D 6) (R 6) [6,9,160,80,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9099 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 11 164 88 50 288 69 197 325), lower := (rows 7 11 164 88 50 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 23 24 16 307 67 131 259), good := (rows 485 493 164 124 508 288 64 128 288) }] }

theorem u9099 : Upper (D 6) (R 6) [6,9,160,80,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9099 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9100 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 88 273 34 100 228 356), lower := (rows 7 11 164 88 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 55 24 16 35 119 183 311), good := (rows 486 494 484 476 508 486 64 128 256) }] }

theorem u9100 : Upper (D 6) (R 6) [6,9,160,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9101 : PairBound 9 := { available := 98, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 88 273 36 98 226 354), lower := (rows 7 11 164 88 273 36 64 128 256), losses := [] }

theorem u9101 : Upper (D 6) (R 6) [6,9,160,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9101 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9102 : Route 9 := (fun mask => (mask,id))

def c9102 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9102 : Upper (D 6) (R 6) [6,9,160,80,257,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80,257,64] 13 (by decide) (choices 1) [2,4,32] r9102 c9102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u832
  · exact u833
  · exact u834

def b9103 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 88 274 33 100 228 356), lower := (rows 7 11 164 88 274 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 41 17 32 100 164 292), good := (rows 478 26 492 88 274 508 64 128 256) }] }

theorem u9103 : Upper (D 6) (R 6) [6,9,160,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9104 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 88 274 36 97 225 353), lower := (rows 7 11 164 88 274 36 64 128 256), losses := [] }

theorem u9104 : Upper (D 6) (R 6) [6,9,160,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9104 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9105 : Route 9 := (fun mask => (mask,id))

def c9105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9105 : Upper (D 6) (R 6) [6,9,160,80,258,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80,258,64] 13 (by decide) (choices 1) [1,4,32] r9105 c9105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u835
  · exact u836
  · exact u837

def r9106 : Route 9 := (fun mask => (mask,id))

def c9106 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9106 : Upper (D 6) (R 6) [6,9,160,80,260,1] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80,260,1] 13 (by decide) (choices 1) [2,32] r9106 c9106
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u838
  · exact u839

def r9107 : Route 9 := (fun mask => (mask,id))

def c9107 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9107 : Upper (D 6) (R 6) [6,9,160,80,260,2] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80,260,2] 13 (by decide) (choices 1) [1,32] r9107 c9107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u840
  · exact u841

def r9108 : Route 9 := (fun mask => (mask,id))

def c9108 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9108 : Upper (D 6) (R 6) [6,9,160,80,260,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80,260,64] 13 (by decide) (choices 1) [1,2,32] r9108 c9108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u842
  · exact u843
  · exact u844

def b9109 : PairBound 9 := { available := 70, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 11 164 88 304 33 70 198 326), lower := (rows 7 11 164 88 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 48 32 65 129 257), good := (rows 454 458 188 88 316 508 64 128 256) }] }

theorem u9109 : Upper (D 6) (R 6) [6,9,160,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9110 : Route 9 := (fun mask => (mask,id))

def c9110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9110 : Upper (D 6) (R 6) [6,9,160,80,288,2] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80,288,2] 13 (by decide) (choices 1) [1,4] r9110 c9110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u845
  · exact u846

def b9111 : PairBound 9 := { available := 67, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 88 304 36 67 195 323), lower := (rows 7 11 164 88 304 36 64 128 256), losses := [] }

theorem u9111 : Upper (D 6) (R 6) [6,9,160,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9111 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9112 : Route 9 := (fun mask => (mask,id))

def c9112 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9112 : Upper (D 6) (R 6) [6,9,160,80,288,64] 13 := by
  apply FastRouting.sound _ _ [6,9,160,80,288,64] 13 (by decide) (choices 1) [1,2,4] r9112 c9112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u847
  · exact u848
  · exact u849

def b9113 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 4, region := 42, targets := 4 }], pairs := [(1,2),(4,1),(4,5)], upper := (rows 7 11 164 104 81 34 340 404 276), lower := (rows 7 11 164 104 81 34 64 128 256), losses := [] }

theorem u9113 : Upper (D 6) (R 6) [6,9,160,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9114 : PairBound 9 := { available := 274, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 7 11 164 104 81 36 338 402 274), lower := (rows 7 11 164 104 81 36 64 128 256), losses := [] }

theorem u9114 : Upper (D 6) (R 6) [6,9,160,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9115 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 164 104 81 48 326 390 262), lower := (rows 7 11 164 104 81 48 64 128 256), losses := [] }

theorem u9115 : Upper (D 6) (R 6) [6,9,160,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9115 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9116 : Route 9 := (fun mask => (mask,id))

def c9116 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9116 : Upper (D 6) (R 6) [6,9,160,96,65,256] 13 := by
  apply FastRouting.sound _ _ [6,9,160,96,65,256] 13 (by decide) (choices 1) [2,4,16] r9116 c9116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u850
  · exact u851
  · exact u852

def b9117 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 336, targets := 1 },{ cop := 0, region := 336, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 164 104 84 33 338 402 274), lower := (rows 7 11 164 104 84 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 40 57 32 67 131 259), good := (rows 470 474 188 124 84 508 64 128 256) }] }

theorem u9117 : Upper (D 6) (R 6) [6,9,160,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9118 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 34 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 7 11 164 104 84 34 337 401 273), lower := (rows 7 11 164 104 84 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 36 40 57 32 67 131 259), good := (rows 469 473 188 124 84 508 64 128 256) }] }

theorem u9118 : Upper (D 6) (R 6) [6,9,160,96,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9119 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 164 104 84 48 323 387 259), lower := (rows 7 11 164 104 84 48 64 128 256), losses := [] }

theorem u9119 : Upper (D 6) (R 6) [6,9,160,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9119 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9119
end Delivery.IrregularNine14.P06
