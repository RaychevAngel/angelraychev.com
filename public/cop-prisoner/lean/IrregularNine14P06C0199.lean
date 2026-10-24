import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0035
import IrregularNine14P06C0036

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r11940 : Route 9 := (fun mask => (mask,id))

def c11940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11940 : Upper (D 6) (R 6) [10,33,18,384,68,64] 13 := by
  apply FastRouting.sound _ _ [10,33,18,384,68,64] 13 (by decide) (choices 1) [1,4,32] r11940 c11940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2147
  · exact u2148
  · exact u2149

def b11941 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 22 392 112 33 68 196 324), lower := (rows 11 35 22 392 112 33 64 128 256), losses := [] }

theorem u11941 : Upper (D 6) (R 6) [10,33,18,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11942 : Route 9 := (fun mask => (mask,id))

def c11942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11942 : Upper (D 6) (R 6) [10,33,18,384,96,4] 13 := by
  apply FastRouting.sound _ _ [10,33,18,384,96,4] 13 (by decide) (choices 1) [1,4] r11942 c11942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2150
  · exact u2151

def b11943 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 35 22 392 112 96 69 133 261), lower := (rows 11 35 22 392 112 96 64 128 256), losses := [] }

theorem u11943 : Upper (D 6) (R 6) [10,33,18,384,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11944 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 73 148 34 324 452 324), lower := (rows 11 35 52 73 148 34 64 128 256), losses := [] }

theorem u11944 : Upper (D 6) (R 6) [10,33,48,65,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11945 : PairBound 9 := { available := 322, camps := [{ cop := 7, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 73 148 36 322 450 322), lower := (rows 11 35 52 73 148 36 64 128 256), losses := [] }

theorem u11945 : Upper (D 6) (R 6) [10,33,48,65,132,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11946 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 52 73 148 96 326 390 262), lower := (rows 11 35 52 73 148 96 64 128 256), losses := [] }

theorem u11946 : Upper (D 6) (R 6) [10,33,48,65,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11947 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 52 73 148 288 70 198 326), lower := (rows 11 35 52 73 148 288 64 128 256), losses := [] }

theorem u11947 : Upper (D 6) (R 6) [10,33,48,65,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11947 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11948 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 73 208 34 324 388 260), lower := (rows 11 35 52 73 208 34 64 128 256), losses := [] }

theorem u11948 : Upper (D 6) (R 6) [10,33,48,65,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11949 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 73 208 36 326 390 262), lower := (rows 11 35 52 73 208 36 64 128 256), losses := [] }

theorem u11949 : Upper (D 6) (R 6) [10,33,48,65,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11950 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 500, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 52 73 208 288 70 134 262), lower := (rows 11 35 52 73 208 288 64 128 256), losses := [] }

theorem u11950 : Upper (D 6) (R 6) [10,33,48,65,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11950 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11951 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 73 400 34 68 196 324), lower := (rows 11 35 52 73 400 34 64 128 256), losses := [] }

theorem u11951 : Upper (D 6) (R 6) [10,33,48,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11952 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 73 400 36 70 198 326), lower := (rows 11 35 52 73 400 36 64 128 256), losses := [] }

theorem u11952 : Upper (D 6) (R 6) [10,33,48,65,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11953 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 11, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 52 73 400 96 70 134 262), lower := (rows 11 35 52 73 400 96 64 128 256), losses := [] }

theorem u11953 : Upper (D 6) (R 6) [10,33,48,65,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11953 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11954 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 52 76 82 33 452 388 388), lower := (rows 11 35 52 76 82 33 64 128 256), losses := [] }

theorem u11954 : Upper (D 6) (R 6) [10,33,48,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11955 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 52 76 82 36 449 385 385), lower := (rows 11 35 52 76 82 36 64 128 256), losses := [] }

theorem u11955 : Upper (D 6) (R 6) [10,33,48,68,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11956 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 52 76 82 160 325 389 261), lower := (rows 11 35 52 76 82 160 64 128 256), losses := [] }

theorem u11956 : Upper (D 6) (R 6) [10,33,48,68,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11956 [(5,7)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11957 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 76 145 34 324 452 324), lower := (rows 11 35 52 76 145 34 64 128 256), losses := [] }

theorem u11957 : Upper (D 6) (R 6) [10,33,48,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11958 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 35 52 76 145 36 322 450 322), lower := (rows 11 35 52 76 145 36 64 128 256), losses := [] }

theorem u11958 : Upper (D 6) (R 6) [10,33,48,68,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11959 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 52 76 145 96 326 390 262), lower := (rows 11 35 52 76 145 96 64 128 256), losses := [] }

theorem u11959 : Upper (D 6) (R 6) [10,33,48,68,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11960 : Route 9 := (fun mask => (mask,id))

def c11960 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11960 : Upper (D 6) (R 6) [10,33,48,68,129,256] 13 := by
  apply FastRouting.sound _ _ [10,33,48,68,129,256] 13 (by decide) (choices 1) [2,4] r11960 c11960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2152
  · exact u2153

def b11961 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 76 146 33 324 452 324), lower := (rows 11 35 52 76 146 33 64 128 256), losses := [] }

theorem u11961 : Upper (D 6) (R 6) [10,33,48,68,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11961 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11962 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 76 146 36 321 449 321), lower := (rows 11 35 52 76 146 36 64 128 256), losses := [] }

theorem u11962 : Upper (D 6) (R 6) [10,33,48,68,130,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11962 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11963 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 52 76 146 96 325 389 261), lower := (rows 11 35 52 76 146 96 64 128 256), losses := [] }

theorem u11963 : Upper (D 6) (R 6) [10,33,48,68,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11963 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11964 : Route 9 := (fun mask => (mask,id))

def c11964 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11964 : Upper (D 6) (R 6) [10,33,48,68,130,256] 13 := by
  apply FastRouting.sound _ _ [10,33,48,68,130,256] 13 (by decide) (choices 1) [1,4] r11964 c11964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2154
  · exact u2155

def b11965 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 52 76 148 33 322 450 322), lower := (rows 11 35 52 76 148 33 64 128 256), losses := [] }

theorem u11965 : Upper (D 6) (R 6) [10,33,48,68,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11965 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11966 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 52 76 148 34 321 449 321), lower := (rows 11 35 52 76 148 34 64 128 256), losses := [] }

theorem u11966 : Upper (D 6) (R 6) [10,33,48,68,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11966 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11967 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 52 76 148 96 323 387 259), lower := (rows 11 35 52 76 148 96 64 128 256), losses := [] }

theorem u11967 : Upper (D 6) (R 6) [10,33,48,68,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11967 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11968 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 291, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 52 76 148 288 67 195 323), lower := (rows 11 35 52 76 148 288 64 128 256), losses := [] }

theorem u11968 : Upper (D 6) (R 6) [10,33,48,68,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11968 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11969 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 52 76 208 33 326 390 262), lower := (rows 11 35 52 76 208 33 64 128 256), losses := [] }

theorem u11969 : Upper (D 6) (R 6) [10,33,48,68,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11969 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11970 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 52 76 208 34 325 389 261), lower := (rows 11 35 52 76 208 34 64 128 256), losses := [] }

theorem u11970 : Upper (D 6) (R 6) [10,33,48,68,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11970 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11971 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 35 52 76 208 36 323 387 259), lower := (rows 11 35 52 76 208 36 64 128 256), losses := [] }

theorem u11971 : Upper (D 6) (R 6) [10,33,48,68,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11971 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11972 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 52 76 208 288 71 135 263), lower := (rows 11 35 52 76 208 288 64 128 256), losses := [] }

theorem u11972 : Upper (D 6) (R 6) [10,33,48,68,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11972 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11973 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 76 400 33 70 198 326), lower := (rows 11 35 52 76 400 33 64 128 256), losses := [] }

theorem u11973 : Upper (D 6) (R 6) [10,33,48,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11973 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11974 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 76 400 34 69 197 325), lower := (rows 11 35 52 76 400 34 64 128 256), losses := [] }

theorem u11974 : Upper (D 6) (R 6) [10,33,48,68,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11974 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11975 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 76 400 36 67 195 323), lower := (rows 11 35 52 76 400 36 64 128 256), losses := [] }

theorem u11975 : Upper (D 6) (R 6) [10,33,48,68,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11975 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11976 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 3, region := 35, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 11 35 52 76 400 96 71 135 263), lower := (rows 11 35 52 76 400 96 64 128 256), losses := [] }

theorem u11976 : Upper (D 6) (R 6) [10,33,48,68,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11976 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11977 : PairBound 9 := { available := 324, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 137 84 34 324 452 324), lower := (rows 11 35 52 137 84 34 64 128 256), losses := [] }

theorem u11977 : Upper (D 6) (R 6) [10,33,48,129,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11977 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11978 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 35 52 137 84 36 322 450 322), lower := (rows 11 35 52 137 84 36 64 128 256), losses := [] }

theorem u11978 : Upper (D 6) (R 6) [10,33,48,129,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11978 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11979 : PairBound 9 := { available := 262, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 52 137 84 96 326 390 262), lower := (rows 11 35 52 137 84 96 64 128 256), losses := [] }

theorem u11979 : Upper (D 6) (R 6) [10,33,48,129,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11979 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11980 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 372, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 35 52 137 84 288 70 198 326), lower := (rows 11 35 52 137 84 288 64 128 256), losses := [] }

theorem u11980 : Upper (D 6) (R 6) [10,33,48,129,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11980 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11981 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 137 276 34 68 196 324), lower := (rows 11 35 52 137 276 34 64 128 256), losses := [] }

theorem u11981 : Upper (D 6) (R 6) [10,33,48,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11981 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11982 : PairBound 9 := { available := 66, camps := [{ cop := 8, region := 52, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 137 276 36 66 194 322), lower := (rows 11 35 52 137 276 36 64 128 256), losses := [] }

theorem u11982 : Upper (D 6) (R 6) [10,33,48,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11982 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11983 : Route 9 := (fun mask => (mask,id))

def c11983 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11983 : Upper (D 6) (R 6) [10,33,48,129,260,64] 13 := by
  apply FastRouting.sound _ _ [10,33,48,129,260,64] 13 (by decide) (choices 1) [2,4] r11983 c11983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2156
  · exact u2157

def b11984 : PairBound 9 := { available := 68, camps := [{ cop := 7, region := 43, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 137 336 34 68 196 324), lower := (rows 11 35 52 137 336 34 64 128 256), losses := [] }

theorem u11984 : Upper (D 6) (R 6) [10,33,48,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11984 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11985 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 137 336 36 70 198 326), lower := (rows 11 35 52 137 336 36 64 128 256), losses := [] }

theorem u11985 : Upper (D 6) (R 6) [10,33,48,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11985 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11986 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 52 137 336 96 70 134 262), lower := (rows 11 35 52 137 336 96 64 128 256), losses := [] }

theorem u11986 : Upper (D 6) (R 6) [10,33,48,129,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11986 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11987 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 140 81 34 324 452 324), lower := (rows 11 35 52 140 81 34 64 128 256), losses := [] }

theorem u11987 : Upper (D 6) (R 6) [10,33,48,132,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11987 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11988 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 11 35 52 140 81 36 322 450 322), lower := (rows 11 35 52 140 81 36 64 128 256), losses := [] }

theorem u11988 : Upper (D 6) (R 6) [10,33,48,132,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11988 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11989 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 52 140 81 96 326 390 262), lower := (rows 11 35 52 140 81 96 64 128 256), losses := [] }

theorem u11989 : Upper (D 6) (R 6) [10,33,48,132,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11989 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11990 : Route 9 := (fun mask => (mask,id))

def c11990 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11990 : Upper (D 6) (R 6) [10,33,48,132,65,256] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,65,256] 13 (by decide) (choices 1) [2,4] r11990 c11990
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2158
  · exact u2159

def b11991 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 140 82 33 324 452 324), lower := (rows 11 35 52 140 82 33 64 128 256), losses := [] }

theorem u11991 : Upper (D 6) (R 6) [10,33,48,132,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11991 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11992 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 35 52 140 82 36 321 449 321), lower := (rows 11 35 52 140 82 36 64 128 256), losses := [] }

theorem u11992 : Upper (D 6) (R 6) [10,33,48,132,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11992 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11993 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 35 52 140 82 96 325 389 261), lower := (rows 11 35 52 140 82 96 64 128 256), losses := [] }

theorem u11993 : Upper (D 6) (R 6) [10,33,48,132,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11993 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r11994 : Route 9 := (fun mask => (mask,id))

def c11994 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11994 : Upper (D 6) (R 6) [10,33,48,132,66,256] 13 := by
  apply FastRouting.sound _ _ [10,33,48,132,66,256] 13 (by decide) (choices 1) [1,4] r11994 c11994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2160
  · exact u2161

def b11995 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 35 52 140 84 33 322 450 322), lower := (rows 11 35 52 140 84 33 64 128 256), losses := [] }

theorem u11995 : Upper (D 6) (R 6) [10,33,48,132,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11995 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11996 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 35 52 140 84 34 321 449 321), lower := (rows 11 35 52 140 84 34 64 128 256), losses := [] }

theorem u11996 : Upper (D 6) (R 6) [10,33,48,132,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11996 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11997 : PairBound 9 := { available := 259, camps := [{ cop := 5, region := 20, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 35 52 140 84 96 323 387 259), lower := (rows 11 35 52 140 84 96 64 128 256), losses := [] }

theorem u11997 : Upper (D 6) (R 6) [10,33,48,132,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11997 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11998 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 52 140 84 288 67 195 323), lower := (rows 11 35 52 140 84 288 64 128 256), losses := [] }

theorem u11998 : Upper (D 6) (R 6) [10,33,48,132,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11998 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b11999 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 35, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 35 52 140 273 34 68 196 324), lower := (rows 11 35 52 140 273 34 64 128 256), losses := [] }

theorem u11999 : Upper (D 6) (R 6) [10,33,48,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b11999 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u11999
end Delivery.IrregularNine14.P06
