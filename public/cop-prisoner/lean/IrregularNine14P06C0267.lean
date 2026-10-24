import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0064
import IrregularNine14P06C0065

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16020 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 37 280 112 34 69 197 325), lower := (rows 11 134 37 280 112 34 64 128 256), losses := [] }

theorem u16020 : Upper (D 6) (R 6) [10,132,33,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16021 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(2,6)], upper := (rows 11 134 37 280 112 36 67 195 323), lower := (rows 11 134 37 280 112 36 64 128 256), losses := [] }

theorem u16021 : Upper (D 6) (R 6) [10,132,33,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16022 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 37 280 112 96 71 135 263), lower := (rows 11 134 37 280 112 96 64 128 256), losses := [] }

theorem u16022 : Upper (D 6) (R 6) [10,132,33,272,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16023 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 134 37 296 81 34 84 212 340), lower := (rows 11 134 37 296 81 34 64 128 256), losses := [] }

theorem u16023 : Upper (D 6) (R 6) [10,132,33,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16024 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 134 37 296 81 36 82 210 338), lower := (rows 11 134 37 296 81 36 64 128 256), losses := [] }

theorem u16024 : Upper (D 6) (R 6) [10,132,33,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16025 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 134 37 296 81 48 70 198 326), lower := (rows 11 134 37 296 81 48 64 128 256), losses := [] }

theorem u16025 : Upper (D 6) (R 6) [10,132,33,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16025 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16026 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 134 37 296 81 96 86 150 278), lower := (rows 11 134 37 296 81 96 64 128 256), losses := [] }

theorem u16026 : Upper (D 6) (R 6) [10,132,33,288,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16027 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 296 82 33 84 212 340), lower := (rows 11 134 37 296 82 33 64 128 256), losses := [] }

theorem u16027 : Upper (D 6) (R 6) [10,132,33,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16028 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(2,6),(4,2)], upper := (rows 11 134 37 296 82 36 81 209 337), lower := (rows 11 134 37 296 82 36 64 128 256), losses := [] }

theorem u16028 : Upper (D 6) (R 6) [10,132,33,288,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16029 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 11 134 37 296 82 48 69 197 325), lower := (rows 11 134 37 296 82 48 64 128 256), losses := [] }

theorem u16029 : Upper (D 6) (R 6) [10,132,33,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16029 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16030 : Route 9 := (fun mask => (mask,id))

def c16030 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16030 : Upper (D 6) (R 6) [10,132,33,288,66,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,288,66,64] 13 (by decide) (choices 1) [1,4,16] r16030 c16030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3887
  · exact u3888
  · exact u3889

def b16031 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 296 84 33 82 210 338), lower := (rows 11 134 37 296 84 33 64 128 256), losses := [] }

theorem u16031 : Upper (D 6) (R 6) [10,132,33,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16032 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 11 134 37 296 84 34 81 209 337), lower := (rows 11 134 37 296 84 34 64 128 256), losses := [] }

theorem u16032 : Upper (D 6) (R 6) [10,132,33,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16033 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 11 134 37 296 84 48 67 195 323), lower := (rows 11 134 37 296 84 48 64 128 256), losses := [] }

theorem u16033 : Upper (D 6) (R 6) [10,132,33,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16033 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16034 : Route 9 := (fun mask => (mask,id))

def c16034 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16034 : Upper (D 6) (R 6) [10,132,33,288,68,64] 13 := by
  apply FastRouting.sound _ _ [10,132,33,288,68,64] 13 (by decide) (choices 1) [1,2,16] r16034 c16034
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3890
  · exact u3891
  · exact u3892

def b16035 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 328 50 33 84 212 340), lower := (rows 11 134 37 328 50 33 64 128 256), losses := [] }

theorem u16035 : Upper (D 6) (R 6) [10,132,33,320,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16036 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 329, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 37 328 50 36 81 209 337), lower := (rows 11 134 37 328 50 36 64 128 256), losses := [] }

theorem u16036 : Upper (D 6) (R 6) [10,132,33,320,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16037 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 134 37 328 50 48 69 197 325), lower := (rows 11 134 37 328 50 48 64 128 256), losses := [] }

theorem u16037 : Upper (D 6) (R 6) [10,132,33,320,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16037 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16038 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 146, targets := 64 }], pairs := [(1,6),(4,0),(4,6)], upper := (rows 11 134 37 328 50 96 85 149 277), lower := (rows 11 134 37 328 50 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 104 64 128 256), good := (rows 58 134 52 360 50 96 96 128 256) }] }

theorem u16038 : Upper (D 6) (R 6) [10,132,33,320,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16039 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(3,1),(4,1)], upper := (rows 11 134 37 328 81 34 116 180 308), lower := (rows 11 134 37 328 81 34 64 128 256), losses := [] }

theorem u16039 : Upper (D 6) (R 6) [10,132,33,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16040 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,6),(2,1),(2,6)], upper := (rows 11 134 37 328 81 36 114 178 306), lower := (rows 11 134 37 328 81 36 64 128 256), losses := [] }

theorem u16040 : Upper (D 6) (R 6) [10,132,33,320,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16041 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 11 134 37 328 81 48 102 166 294), lower := (rows 11 134 37 328 81 48 64 128 256), losses := [] }

theorem u16041 : Upper (D 6) (R 6) [10,132,33,320,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16041 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16042 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 328 82 33 116 180 308), lower := (rows 11 134 37 328 82 33 64 128 256), losses := [] }

theorem u16042 : Upper (D 6) (R 6) [10,132,33,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16043 : Route 9 := (fun mask => (mask,id))

def c16043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16043 : Upper (D 6) (R 6) [10,132,33,320,66,4] 13 := by
  apply FastRouting.sound _ _ [10,132,33,320,66,4] 13 (by decide) (choices 1) [1,16,32] r16043 c16043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3893
  · exact u3894
  · exact u3895

def b16044 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 328, targets := 2 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,6),(3,1)], upper := (rows 11 134 37 328 82 48 101 165 293), lower := (rows 11 134 37 328 82 48 64 128 256), losses := [] }

theorem u16044 : Upper (D 6) (R 6) [10,132,33,320,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16044 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16045 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 328 84 33 114 178 306), lower := (rows 11 134 37 328 84 33 64 128 256), losses := [] }

theorem u16045 : Upper (D 6) (R 6) [10,132,33,320,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16046 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 37 328 84 34 113 177 305), lower := (rows 11 134 37 328 84 34 64 128 256), losses := [] }

theorem u16046 : Upper (D 6) (R 6) [10,132,33,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16047 : Route 9 := (fun mask => (mask,id))

def c16047 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16047 : Upper (D 6) (R 6) [10,132,33,320,68,16] 13 := by
  apply FastRouting.sound _ _ [10,132,33,320,68,16] 13 (by decide) (choices 1) [1,2,32] r16047 c16047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3896
  · exact u3897
  · exact u3898

def b16048 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 134 37 328 112 33 86 150 278), lower := (rows 11 134 37 328 112 33 64 128 256), losses := [] }

theorem u16048 : Upper (D 6) (R 6) [10,132,33,320,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16049 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 344, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 37 328 112 34 85 149 277), lower := (rows 11 134 37 328 112 34 64 128 256), losses := [] }

theorem u16049 : Upper (D 6) (R 6) [10,132,33,320,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16050 : Route 9 := (fun mask => (mask,id))

def c16050 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16050 : Upper (D 6) (R 6) [10,132,33,320,96,4] 13 := by
  apply FastRouting.sound _ _ [10,132,33,320,96,4] 13 (by decide) (choices 1) [1,2,16] r16050 c16050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3899
  · exact u3900
  · exact u3901

def b16051 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 37 328 112 48 71 135 263), lower := (rows 11 134 37 328 112 48 64 128 256), losses := [] }

theorem u16051 : Upper (D 6) (R 6) [10,132,33,320,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16051 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16052 : PairBound 9 := { available := 352, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 25 84 33 352 480 352), lower := (rows 11 134 38 25 84 33 64 128 256), losses := [] }

theorem u16052 : Upper (D 6) (R 6) [10,132,34,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16053 : Route 9 := (fun mask => (mask,id))

def c16053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u16053 : Upper (D 6) (R 6) [10,132,34,17,68,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,68,64] 13 (by decide) (choices 1) [1,32,256] r16053 c16053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3902
  · exact u3903
  · exact u3904

def r16054 : Route 9 := (fun mask => (mask,id))

def c16054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16054 : Upper (D 6) (R 6) [10,132,34,17,68,256] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,68,256] 13 (by decide) (choices 1) [1,32] r16054 c16054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3905
  · exact u3906

def b16055 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 25 112 33 324 452 324), lower := (rows 11 134 38 25 112 33 64 128 256), losses := [] }

theorem u16055 : Upper (D 6) (R 6) [10,132,34,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16056 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 25 112 36 321 449 321), lower := (rows 11 134 38 25 112 36 64 128 256), losses := [] }

theorem u16056 : Upper (D 6) (R 6) [10,132,34,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16057 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 38 25 112 96 325 389 261), lower := (rows 11 134 38 25 112 96 64 128 256), losses := [] }

theorem u16057 : Upper (D 6) (R 6) [10,132,34,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16058 : Route 9 := (fun mask => (mask,id))

def c16058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16058 : Upper (D 6) (R 6) [10,132,34,17,96,256] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,96,256] 13 (by decide) (choices 1) [1,4] r16058 c16058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3907
  · exact u3908

def b16059 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 25 276 33 96 224 352), lower := (rows 11 134 38 25 276 33 64 128 256), losses := [] }

theorem u16059 : Upper (D 6) (R 6) [10,132,34,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16059 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16060 : Route 9 := (fun mask => (mask,id))

def c16060 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16060 : Upper (D 6) (R 6) [10,132,34,17,260,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,260,64] 13 (by decide) (choices 1) [1,32] r16060 c16060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3909
  · exact u3910

def b16061 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 25 304 33 68 196 324), lower := (rows 11 134 38 25 304 33 64 128 256), losses := [] }

theorem u16061 : Upper (D 6) (R 6) [10,132,34,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16062 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 25 304 36 65 193 321), lower := (rows 11 134 38 25 304 36 64 128 256), losses := [] }

theorem u16062 : Upper (D 6) (R 6) [10,132,34,17,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16063 : Route 9 := (fun mask => (mask,id))

def c16063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16063 : Upper (D 6) (R 6) [10,132,34,17,288,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,288,64] 13 (by decide) (choices 1) [1,4] r16063 c16063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3911
  · exact u3912

def b16064 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 38 25 336 33 100 228 356), lower := (rows 11 134 38 25 336 33 64 128 256), losses := [] }

theorem u16064 : Upper (D 6) (R 6) [10,132,34,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16065 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 25 336 36 97 225 353), lower := (rows 11 134 38 25 336 36 64 128 256), losses := [] }

theorem u16065 : Upper (D 6) (R 6) [10,132,34,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16066 : Route 9 := (fun mask => (mask,id))

def c16066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16066 : Upper (D 6) (R 6) [10,132,34,17,320,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,17,320,64] 13 (by decide) (choices 1) [1,4,32] r16066 c16066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3913
  · exact u3914
  · exact u3915

def b16067 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 5, region := 454, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 134 38 28 81 33 352 480 352), lower := (rows 11 134 38 28 81 33 64 128 256), losses := [] }

theorem u16067 : Upper (D 6) (R 6) [10,132,34,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16068 : Route 9 := (fun mask => (mask,id))

def c16068 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u16068 : Upper (D 6) (R 6) [10,132,34,20,65,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,20,65,64] 13 (by decide) (choices 1) [1,32,256] r16068 c16068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3916
  · exact u3917
  · exact u3918

def b16069 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 38 28 81 288 97 225 353), lower := (rows 11 134 38 28 81 288 64 128 256), losses := [] }

theorem u16069 : Upper (D 6) (R 6) [10,132,34,20,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16069 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16070 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(4,1),(4,2)], upper := (rows 11 134 38 28 273 33 96 224 352), lower := (rows 11 134 38 28 273 33 64 128 256), losses := [] }

theorem u16070 : Upper (D 6) (R 6) [10,132,34,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16071 : Route 9 := (fun mask => (mask,id))

def c16071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16071 : Upper (D 6) (R 6) [10,132,34,20,257,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,20,257,64] 13 (by decide) (choices 1) [1,32] r16071 c16071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3919
  · exact u3920

def b16072 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(4,1),(4,2)], upper := (rows 11 134 38 28 336 33 97 225 353), lower := (rows 11 134 38 28 336 33 64 128 256), losses := [] }

theorem u16072 : Upper (D 6) (R 6) [10,132,34,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16072 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16073 : Route 9 := (fun mask => (mask,id))

def c16073 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16073 : Upper (D 6) (R 6) [10,132,34,20,320,64] 13 := by
  apply FastRouting.sound _ _ [10,132,34,20,320,64] 13 (by decide) (choices 1) [1,32] r16073 c16073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3921
  · exact u3922

def b16074 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 134 38 56 81 33 324 452 324), lower := (rows 11 134 38 56 81 33 64 128 256), losses := [] }

theorem u16074 : Upper (D 6) (R 6) [10,132,34,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16075 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 134 38 56 81 36 321 449 321), lower := (rows 11 134 38 56 81 36 64 128 256), losses := [] }

theorem u16075 : Upper (D 6) (R 6) [10,132,34,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16076 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 38 56 81 96 325 389 261), lower := (rows 11 134 38 56 81 96 64 128 256), losses := [] }

theorem u16076 : Upper (D 6) (R 6) [10,132,34,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16077 : Route 9 := (fun mask => (mask,id))

def c16077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16077 : Upper (D 6) (R 6) [10,132,34,48,65,256] 13 := by
  apply FastRouting.sound _ _ [10,132,34,48,65,256] 13 (by decide) (choices 1) [1,4] r16077 c16077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3923
  · exact u3924

def b16078 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 134 38 56 84 33 321 449 321), lower := (rows 11 134 38 56 84 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 33 97 161 289), good := (rows 489 156 508 504 92 481 64 128 256) }] }

theorem u16078 : Upper (D 6) (R 6) [10,132,34,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16079 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 38 56 84 96 321 385 257), lower := (rows 11 134 38 56 84 96 64 128 256), losses := [] }

theorem u16079 : Upper (D 6) (R 6) [10,132,34,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u16079
end Delivery.IrregularNine14.P06
