import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0264
import IrregularNine14P06C0265
import IrregularNine14P06C0266

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33060 : Route 9 := (fun mask => (mask,id))

def c33060 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33060 : Upper (D 6) (R 6) [10,132,33,20,320] 13 := by
  apply FastRouting.sound _ _ [10,132,33,20,320] 13 (by decide) (choices 1) [1,2,64] r33060 c33060
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15888
  · exact u15889
  · exact u15890

def b33061 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 37 56 19 356 324 452 324), lower := (rows 11 134 37 56 19 32 64 128 256), losses := [] }

theorem u33061 : Upper (D 6) (R 6) [10,132,33,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33062 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 24, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 11 134 37 56 21 354 322 450 322), lower := (rows 11 134 37 56 21 32 64 128 256), losses := [] }

theorem u33062 : Upper (D 6) (R 6) [10,132,33,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33063 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 37 56 22 353 321 449 321), lower := (rows 11 134 37 56 22 32 64 128 256), losses := [] }

theorem u33063 : Upper (D 6) (R 6) [10,132,33,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33064 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 11 134 37 56 81 358 326 454 326), lower := (rows 11 134 37 56 81 32 64 128 256), losses := [] }

theorem u33064 : Upper (D 6) (R 6) [10,132,33,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33065 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 134 37 56 82 357 325 453 325), lower := (rows 11 134 37 56 82 32 64 128 256), losses := [] }

theorem u33065 : Upper (D 6) (R 6) [10,132,33,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33066 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 134 37 56 84 355 323 451 323), lower := (rows 11 134 37 56 84 32 64 128 256), losses := [{ target := 5, region := (rows 9 22 4 8 22 0 77 141 269), good := (rows 475 470 471 475 470 0 64 128 256) }] }

theorem u33066 : Upper (D 6) (R 6) [10,132,33,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33066 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33067 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 11 134 37 56 273 102 70 198 326), lower := (rows 11 134 37 56 273 32 64 128 256), losses := [] }

theorem u33067 : Upper (D 6) (R 6) [10,132,33,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33068 : PairBound 9 := { available := 69, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 134 37 56 274 101 69 197 325), lower := (rows 11 134 37 56 274 32 64 128 256), losses := [] }

theorem u33068 : Upper (D 6) (R 6) [10,132,33,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33069 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 134 37 56 276 99 67 195 323), lower := (rows 11 134 37 56 276 32 64 128 256), losses := [{ target := 5, region := (rows 9 22 4 8 22 0 77 141 269), good := (rows 475 470 471 475 470 0 64 128 256) }] }

theorem u33069 : Upper (D 6) (R 6) [10,132,33,48,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33070 : Route 9 := (fun mask => (mask,id))

def c33070 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33070 : Upper (D 6) (R 6) [10,132,33,48,320] 13 := by
  apply FastRouting.sound _ _ [10,132,33,48,320] 13 (by decide) (choices 1) [1,2,4,64] r33070 c33070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15891
  · exact u15892
  · exact u15893
  · exact u15894

def b33071 : PairBound 9 := { available := 368, camps := [{ cop := 1, region := 16, targets := 96 },{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 11 134 37 73 22 368 368 496 368), lower := (rows 11 134 37 73 22 32 64 128 256), losses := [] }

theorem u33071 : Upper (D 6) (R 6) [10,132,33,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33072 : Route 9 := (fun mask => (mask,id))

def c33072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u33072 : Upper (D 6) (R 6) [10,132,33,65,34] 13 := by
  apply FastRouting.sound _ _ [10,132,33,65,34] 13 (by decide) (choices 1) [4,16,64,256] r33072 c33072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15895
  · exact u15896
  · exact u15897
  · exact u15898

def b33073 : PairBound 9 := { available := 338, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 37 73 52 370 338 466 338), lower := (rows 11 134 37 73 52 32 64 128 256), losses := [] }

theorem u33073 : Upper (D 6) (R 6) [10,132,33,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33074 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 37 73 82 308 372 436 308), lower := (rows 11 134 37 73 82 32 64 128 256), losses := [] }

theorem u33074 : Upper (D 6) (R 6) [10,132,33,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33075 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 4, region := 418, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 134 37 73 84 306 370 434 306), lower := (rows 11 134 37 73 84 32 64 128 256), losses := [] }

theorem u33075 : Upper (D 6) (R 6) [10,132,33,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33076 : Route 9 := (fun mask => (mask,id))

def c33076 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33076 : Upper (D 6) (R 6) [10,132,33,65,96] 13 := by
  apply FastRouting.sound _ _ [10,132,33,65,96] 13 (by decide) (choices 1) [2,4,16,256] r33076 c33076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15899
  · exact u15900
  · exact u15901
  · exact u15902

def r33077 : Route 9 := (fun mask => (mask,id))

def c33077 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33077 : Upper (D 6) (R 6) [10,132,33,65,258] 13 := by
  apply FastRouting.sound _ _ [10,132,33,65,258] 13 (by decide) (choices 1) [4,16,64] r33077 c33077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15903
  · exact u15904
  · exact u15905

def r33078 : Route 9 := (fun mask => (mask,id))

def c33078 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33078 : Upper (D 6) (R 6) [10,132,33,65,260] 13 := by
  apply FastRouting.sound _ _ [10,132,33,65,260] 13 (by decide) (choices 1) [2,16,64] r33078 c33078
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15906
  · exact u15907
  · exact u15908

def r33079 : Route 9 := (fun mask => (mask,id))

def c33079 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33079 : Upper (D 6) (R 6) [10,132,33,65,288] 13 := by
  apply FastRouting.sound _ _ [10,132,33,65,288] 13 (by decide) (choices 1) [2,4,16,64] r33079 c33079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15909
  · exact u15910
  · exact u15911
  · exact u15912

def r33080 : Route 9 := (fun mask => (mask,id))

def c33080 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33080 : Upper (D 6) (R 6) [10,132,33,65,320] 13 := by
  apply FastRouting.sound _ _ [10,132,33,65,320] 13 (by decide) (choices 1) [2,4,16] r33080 c33080
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15913
  · exact u15914
  · exact u15915

def b33081 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 134 37 76 19 368 368 496 368), lower := (rows 11 134 37 76 19 32 64 128 256), losses := [] }

theorem u33081 : Upper (D 6) (R 6) [10,132,33,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33081 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33082 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 11 134 37 76 49 370 338 466 338), lower := (rows 11 134 37 76 49 32 64 128 256), losses := [] }

theorem u33082 : Upper (D 6) (R 6) [10,132,33,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33083 : Route 9 := (fun mask => (mask,id))

def c33083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u33083 : Upper (D 6) (R 6) [10,132,33,68,34] 13 := by
  apply FastRouting.sound _ _ [10,132,33,68,34] 13 (by decide) (choices 1) [1,16,64,256] r33083 c33083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15916
  · exact u15917
  · exact u15918
  · exact u15919

def b33084 : PairBound 9 := { available := 306, camps := [{ cop := 4, region := 422, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,6),(2,6),(4,2)], upper := (rows 11 134 37 76 81 306 370 434 306), lower := (rows 11 134 37 76 81 32 64 128 256), losses := [] }

theorem u33084 : Upper (D 6) (R 6) [10,132,33,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33085 : Route 9 := (fun mask => (mask,id))

def c33085 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33085 : Upper (D 6) (R 6) [10,132,33,68,66] 13 := by
  apply FastRouting.sound _ _ [10,132,33,68,66] 13 (by decide) (choices 1) [1,16,256] r33085 c33085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15920
  · exact u15921
  · exact u15922

def r33086 : Route 9 := (fun mask => (mask,id))

def c33086 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33086 : Upper (D 6) (R 6) [10,132,33,68,96] 13 := by
  apply FastRouting.sound _ _ [10,132,33,68,96] 13 (by decide) (choices 1) [1,2,16,256] r33086 c33086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15923
  · exact u15924
  · exact u15925
  · exact u15926

def r33087 : Route 9 := (fun mask => (mask,id))

def c33087 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33087 : Upper (D 6) (R 6) [10,132,33,68,257] 13 := by
  apply FastRouting.sound _ _ [10,132,33,68,257] 13 (by decide) (choices 1) [2,16,64] r33087 c33087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15927
  · exact u15928
  · exact u15929

def r33088 : Route 9 := (fun mask => (mask,id))

def c33088 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33088 : Upper (D 6) (R 6) [10,132,33,68,258] 13 := by
  apply FastRouting.sound _ _ [10,132,33,68,258] 13 (by decide) (choices 1) [1,16,64] r33088 c33088
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15930
  · exact u15931
  · exact u15932

def r33089 : Route 9 := (fun mask => (mask,id))

def c33089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33089 : Upper (D 6) (R 6) [10,132,33,68,288] 13 := by
  apply FastRouting.sound _ _ [10,132,33,68,288] 13 (by decide) (choices 1) [1,2,16,64] r33089 c33089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15933
  · exact u15934
  · exact u15935
  · exact u15936

def r33090 : Route 9 := (fun mask => (mask,id))

def c33090 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33090 : Upper (D 6) (R 6) [10,132,33,68,320] 13 := by
  apply FastRouting.sound _ _ [10,132,33,68,320] 13 (by decide) (choices 1) [1,2,16] r33090 c33090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15937
  · exact u15938
  · exact u15939

def b33091 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 37 88 19 356 356 484 356), lower := (rows 11 134 37 88 19 32 64 128 256), losses := [] }

theorem u33091 : Upper (D 6) (R 6) [10,132,33,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33092 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 134 37 88 21 354 354 482 354), lower := (rows 11 134 37 88 21 32 64 128 256), losses := [] }

theorem u33092 : Upper (D 6) (R 6) [10,132,33,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33092 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33093 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 37 88 22 353 353 481 353), lower := (rows 11 134 37 88 22 32 64 128 256), losses := [] }

theorem u33093 : Upper (D 6) (R 6) [10,132,33,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33094 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 11 134 37 88 49 358 326 454 326), lower := (rows 11 134 37 88 49 32 64 128 256), losses := [] }

theorem u33094 : Upper (D 6) (R 6) [10,132,33,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33095 : Route 9 := (fun mask => (mask,id))

def c33095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33095 : Upper (D 6) (R 6) [10,132,33,80,34] 13 := by
  apply FastRouting.sound _ _ [10,132,33,80,34] 13 (by decide) (choices 1) [1,4,64,256] r33095 c33095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15940
  · exact u15941
  · exact u15942
  · exact u15943

def b33096 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 37 88 52 355 323 451 323), lower := (rows 11 134 37 88 52 32 64 128 256), losses := [] }

theorem u33096 : Upper (D 6) (R 6) [10,132,33,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33096 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33097 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 37 88 81 294 358 422 294), lower := (rows 11 134 37 88 81 32 64 128 256), losses := [] }

theorem u33097 : Upper (D 6) (R 6) [10,132,33,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33098 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 9, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 37 88 82 293 357 421 293), lower := (rows 11 134 37 88 82 32 64 128 256), losses := [] }

theorem u33098 : Upper (D 6) (R 6) [10,132,33,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33098 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33099 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 37 88 84 291 355 419 291), lower := (rows 11 134 37 88 84 32 64 128 256), losses := [] }

theorem u33099 : Upper (D 6) (R 6) [10,132,33,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33099 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33100 : PairBound 9 := { available := 263, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 37 88 112 295 327 391 263), lower := (rows 11 134 37 88 112 32 64 128 256), losses := [] }

theorem u33100 : Upper (D 6) (R 6) [10,132,33,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33100 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33101 : Route 9 := (fun mask => (mask,id))

def c33101 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33101 : Upper (D 6) (R 6) [10,132,33,80,257] 13 := by
  apply FastRouting.sound _ _ [10,132,33,80,257] 13 (by decide) (choices 1) [2,4,64] r33101 c33101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15944
  · exact u15945
  · exact u15946

def r33102 : Route 9 := (fun mask => (mask,id))

def c33102 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33102 : Upper (D 6) (R 6) [10,132,33,80,258] 13 := by
  apply FastRouting.sound _ _ [10,132,33,80,258] 13 (by decide) (choices 1) [1,4,64] r33102 c33102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15947
  · exact u15948
  · exact u15949

def r33103 : Route 9 := (fun mask => (mask,id))

def c33103 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33103 : Upper (D 6) (R 6) [10,132,33,80,260] 13 := by
  apply FastRouting.sound _ _ [10,132,33,80,260] 13 (by decide) (choices 1) [1,2,64] r33103 c33103
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15950
  · exact u15951
  · exact u15952

def r33104 : Route 9 := (fun mask => (mask,id))

def c33104 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33104 : Upper (D 6) (R 6) [10,132,33,80,288] 13 := by
  apply FastRouting.sound _ _ [10,132,33,80,288] 13 (by decide) (choices 1) [1,2,4,64] r33104 c33104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15953
  · exact u15954
  · exact u15955
  · exact u15956

def b33105 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 37 88 336 39 103 167 295), lower := (rows 11 134 37 88 336 32 64 128 256), losses := [] }

theorem u33105 : Upper (D 6) (R 6) [10,132,33,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33106 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 37 104 19 372 340 468 340), lower := (rows 11 134 37 104 19 32 64 128 256), losses := [] }

theorem u33106 : Upper (D 6) (R 6) [10,132,33,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33107 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 66 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 11 134 37 104 21 370 338 466 338), lower := (rows 11 134 37 104 21 32 64 128 256), losses := [] }

theorem u33107 : Upper (D 6) (R 6) [10,132,33,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33107 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33108 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 37 104 22 369 337 465 337), lower := (rows 11 134 37 104 22 32 64 128 256), losses := [] }

theorem u33108 : Upper (D 6) (R 6) [10,132,33,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33108 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33109 : PairBound 9 := { available := 278, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,5),(1,6),(4,5)], upper := (rows 11 134 37 104 81 310 342 406 278), lower := (rows 11 134 37 104 81 32 64 128 256), losses := [] }

theorem u33109 : Upper (D 6) (R 6) [10,132,33,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33109 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33110 : Route 9 := (fun mask => (mask,id))

def c33110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33110 : Upper (D 6) (R 6) [10,132,33,96,66] 13 := by
  apply FastRouting.sound _ _ [10,132,33,96,66] 13 (by decide) (choices 1) [1,4,16,256] r33110 c33110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15957
  · exact u15958
  · exact u15959
  · exact u15960

def r33111 : Route 9 := (fun mask => (mask,id))

def c33111 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33111 : Upper (D 6) (R 6) [10,132,33,96,68] 13 := by
  apply FastRouting.sound _ _ [10,132,33,96,68] 13 (by decide) (choices 1) [1,2,16,256] r33111 c33111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15961
  · exact u15962
  · exact u15963
  · exact u15964

def r33112 : Route 9 := (fun mask => (mask,id))

def c33112 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33112 : Upper (D 6) (R 6) [10,132,33,96,257] 13 := by
  apply FastRouting.sound _ _ [10,132,33,96,257] 13 (by decide) (choices 1) [2,4,16,64] r33112 c33112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15965
  · exact u15966
  · exact u15967
  · exact u15968

def r33113 : Route 9 := (fun mask => (mask,id))

def c33113 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33113 : Upper (D 6) (R 6) [10,132,33,96,258] 13 := by
  apply FastRouting.sound _ _ [10,132,33,96,258] 13 (by decide) (choices 1) [1,4,16,64] r33113 c33113
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15969
  · exact u15970
  · exact u15971
  · exact u15972

def r33114 : Route 9 := (fun mask => (mask,id))

def c33114 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33114 : Upper (D 6) (R 6) [10,132,33,96,260] 13 := by
  apply FastRouting.sound _ _ [10,132,33,96,260] 13 (by decide) (choices 1) [1,2,16,64] r33114 c33114
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15973
  · exact u15974
  · exact u15975
  · exact u15976

def r33115 : Route 9 := (fun mask => (mask,id))

def c33115 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33115 : Upper (D 6) (R 6) [10,132,33,96,320] 13 := by
  apply FastRouting.sound _ _ [10,132,33,96,320] 13 (by decide) (choices 1) [1,2,4,16] r33115 c33115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15977
  · exact u15978
  · exact u15979
  · exact u15980

def b33116 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 16, targets := 96 },{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 11 134 37 265 22 112 112 240 368), lower := (rows 11 134 37 265 22 32 64 128 256), losses := [] }

theorem u33116 : Upper (D 6) (R 6) [10,132,33,257,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33117 : Route 9 := (fun mask => (mask,id))

def c33117 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33117 : Upper (D 6) (R 6) [10,132,33,257,34] 13 := by
  apply FastRouting.sound _ _ [10,132,33,257,34] 13 (by decide) (choices 1) [4,16,64] r33117 c33117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15981
  · exact u15982
  · exact u15983

def b33118 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 459, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 134 37 265 52 114 82 210 338), lower := (rows 11 134 37 265 52 32 64 128 256), losses := [] }

theorem u33118 : Upper (D 6) (R 6) [10,132,33,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33119 : Route 9 := (fun mask => (mask,id))

def c33119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33119 : Upper (D 6) (R 6) [10,132,33,257,66] 13 := by
  apply FastRouting.sound _ _ [10,132,33,257,66] 13 (by decide) (choices 1) [4,16,64] r33119 c33119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15984
  · exact u15985
  · exact u15986

#print axioms u33119
end Delivery.IrregularNine14.P06
