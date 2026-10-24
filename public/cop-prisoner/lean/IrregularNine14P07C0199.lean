import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0016
import IrregularNine14P07C0017

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11940 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 26 100 168 273 160 67 195 323), lower := (rows 7 26 100 168 273 160 64 128 256), losses := [] }

theorem u11940 : Upper (D 7) (R 7) [6,24,96,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11940 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11941 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,5)], upper := (rows 7 26 100 168 274 33 193 193 449), lower := (rows 7 26 100 168 274 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 25 0 97 161 289), good := (rows 471 26 452 474 274 465 64 128 256) }] }

theorem u11941 : Upper (D 7) (R 7) [6,24,96,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11941 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11942 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 168 274 96 193 129 385), lower := (rows 7 26 100 168 274 96 64 128 256), losses := [] }

theorem u11942 : Upper (D 7) (R 7) [6,24,96,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11942 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11943 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 26 100 168 274 160 65 193 321), lower := (rows 7 26 100 168 274 160 64 128 256), losses := [] }

theorem u11943 : Upper (D 7) (R 7) [6,24,96,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11944 : Route 9 := (fun mask => (mask,id))

def c11944 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11944 : Upper (D 7) (R 7) [6,24,96,160,320,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,320,1] 13 (by decide) (choices 1) [1,2,128] r11944 c11944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1015
  · exact u1016
  · exact u1017

def r11945 : Route 9 := (fun mask => (mask,id))

def c11945 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11945 : Upper (D 7) (R 7) [6,24,96,160,320,2] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,320,2] 13 (by decide) (choices 1) [1,128] r11945 c11945
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1018
  · exact u1019

def b11946 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 26 100 168 336 160 67 131 259), lower := (rows 7 26 100 168 336 160 64 128 256), losses := [] }

theorem u11946 : Upper (D 7) (R 7) [6,24,96,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11947 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,5)], upper := (rows 7 26 100 168 400 33 67 195 323), lower := (rows 7 26 100 168 400 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 49 0 65 129 257), good := (rows 471 26 84 154 400 465 64 128 256) }] }

theorem u11947 : Upper (D 7) (R 7) [6,24,96,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11948 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 26 100 168 400 34 65 193 321), lower := (rows 7 26 100 168 400 34 64 128 256), losses := [] }

theorem u11948 : Upper (D 7) (R 7) [6,24,96,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11949 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 168 400 96 67 131 259), lower := (rows 7 26 100 168 400 96 64 128 256), losses := [] }

theorem u11949 : Upper (D 7) (R 7) [6,24,96,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11950 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 40, targets := 192 },{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0),(3,6),(3,7),(4,0)], upper := (rows 7 26 261 41 208 34 224 224 480), lower := (rows 7 26 261 41 208 34 64 128 256), losses := [] }

theorem u11950 : Upper (D 7) (R 7) [6,24,257,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11951 : Route 9 := (fun mask => (mask,id))

def c11951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11951 : Upper (D 7) (R 7) [6,24,257,33,192,64] 13 := by
  apply FastRouting.sound _ _ [6,24,257,33,192,64] 13 (by decide) (choices 1) [2,32,128] r11951 c11951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1020
  · exact u1021
  · exact u1022

def b11952 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 0, region := 484, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 26 261 42 208 33 224 224 480), lower := (rows 7 26 261 42 208 33 64 128 256), losses := [] }

theorem u11952 : Upper (D 7) (R 7) [6,24,257,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11953 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 26 261 42 208 96 225 161 417), lower := (rows 7 26 261 42 208 96 64 128 256), losses := [] }

theorem u11953 : Upper (D 7) (R 7) [6,24,257,34,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11954 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 218, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 26 261 104 176 33 194 194 450), lower := (rows 7 26 261 104 176 33 64 128 256), losses := [] }

theorem u11954 : Upper (D 7) (R 7) [6,24,257,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11954 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11955 : Route 9 := (fun mask => (mask,id))

def c11955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11955 : Upper (D 7) (R 7) [6,24,257,96,160,2] 13 := by
  apply FastRouting.sound _ _ [6,24,257,96,160,2] 13 (by decide) (choices 1) [1,128] r11955 c11955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1023
  · exact u1024

def b11956 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 26 261 104 176 96 195 131 387), lower := (rows 7 26 261 104 176 96 64 128 256), losses := [] }

theorem u11956 : Upper (D 7) (R 7) [6,24,257,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11957 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 42, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 26 292 41 81 34 192 192 448), lower := (rows 7 26 292 41 81 34 64 128 256), losses := [] }

theorem u11957 : Upper (D 7) (R 7) [6,24,288,33,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11957 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11958 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 42, targets := 128 }], pairs := [(1,5),(1,7),(3,7),(4,5)], upper := (rows 7 26 292 41 81 96 194 130 386), lower := (rows 7 26 292 41 81 96 64 128 256), losses := [] }

theorem u11958 : Upper (D 7) (R 7) [6,24,288,33,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11959 : Route 9 := (fun mask => (mask,id))

def c11959 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11959 : Upper (D 7) (R 7) [6,24,288,33,65,128] 13 := by
  apply FastRouting.sound _ _ [6,24,288,33,65,128] 13 (by decide) (choices 1) [2,128] r11959 c11959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1025
  · exact u1026

def b11960 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 40, targets := 194 },{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(3,7)], upper := (rows 7 26 292 41 208 33 194 194 450), lower := (rows 7 26 292 41 208 33 64 128 256), losses := [] }

theorem u11960 : Upper (D 7) (R 7) [6,24,288,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11961 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 34 },{ cop := 0, region := 40, targets := 192 }], pairs := [(3,6),(3,7),(4,1),(4,5)], upper := (rows 7 26 292 41 208 34 193 193 449), lower := (rows 7 26 292 41 208 34 64 128 256), losses := [] }

theorem u11961 : Upper (D 7) (R 7) [6,24,288,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11962 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,5)], upper := (rows 7 26 292 41 208 96 195 131 387), lower := (rows 7 26 292 41 208 96 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 16 32 0 131 259), good := (rows 391 415 292 429 144 32 0 128 256) }] }

theorem u11962 : Upper (D 7) (R 7) [6,24,288,33,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11963 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 42, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 26 292 42 81 33 192 192 448), lower := (rows 7 26 292 42 81 33 64 128 256), losses := [] }

theorem u11963 : Upper (D 7) (R 7) [6,24,288,34,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11963 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11964 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 26 292 42 81 96 193 129 385), lower := (rows 7 26 292 42 81 96 64 128 256), losses := [] }

theorem u11964 : Upper (D 7) (R 7) [6,24,288,34,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11965 : Route 9 := (fun mask => (mask,id))

def c11965 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11965 : Upper (D 7) (R 7) [6,24,288,34,65,128] 13 := by
  apply FastRouting.sound _ _ [6,24,288,34,65,128] 13 (by decide) (choices 1) [1,128] r11965 c11965
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1027
  · exact u1028

def b11966 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 40, targets := 192 }], pairs := [(2,1),(3,6),(3,7),(4,1)], upper := (rows 7 26 292 42 208 33 193 193 449), lower := (rows 7 26 292 42 208 33 64 128 256), losses := [] }

theorem u11966 : Upper (D 7) (R 7) [6,24,288,34,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11967 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 26 292 42 208 96 193 129 385), lower := (rows 7 26 292 42 208 96 64 128 256), losses := [] }

theorem u11967 : Upper (D 7) (R 7) [6,24,288,34,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11968 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 3, region := 50, targets := 128 }], pairs := [(0,6),(1,7),(2,6),(4,7)], upper := (rows 7 26 292 73 112 33 194 130 386), lower := (rows 7 26 292 73 112 33 64 128 256), losses := [] }

theorem u11968 : Upper (D 7) (R 7) [6,24,288,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11968 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11969 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 50, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 7 26 292 73 112 34 193 129 385), lower := (rows 7 26 292 73 112 34 64 128 256), losses := [] }

theorem u11969 : Upper (D 7) (R 7) [6,24,288,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11969 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11970 : Route 9 := (fun mask => (mask,id))

def c11970 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11970 : Upper (D 7) (R 7) [6,24,288,65,96,128] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,96,128] 13 (by decide) (choices 1) [1,2,128] r11970 c11970
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1029
  · exact u1030
  · exact u1031

def b11971 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 452, targets := 3 }], pairs := [(2,0),(2,1),(3,1),(4,1)], upper := (rows 7 26 292 73 145 34 224 224 480), lower := (rows 7 26 292 73 145 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 36 9 17 32 100 164 292), good := (rows 477 24 484 89 153 484 64 128 256) }] }

theorem u11971 : Upper (D 7) (R 7) [6,24,288,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11972 : Route 9 := (fun mask => (mask,id))

def c11972 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11972 : Upper (D 7) (R 7) [6,24,288,65,129,64] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,129,64] 13 (by decide) (choices 1) [2,32,128] r11972 c11972
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1032
  · exact u1033
  · exact u1034

def b11973 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 5, region := 452, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(3,1)], upper := (rows 7 26 292 73 146 33 224 224 480), lower := (rows 7 26 292 73 146 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 36 8 17 32 100 164 292), good := (rows 470 26 484 90 146 500 64 128 256) }] }

theorem u11973 : Upper (D 7) (R 7) [6,24,288,65,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11974 : Route 9 := (fun mask => (mask,id))

def c11974 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11974 : Upper (D 7) (R 7) [6,24,288,65,130,64] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,130,64] 13 (by decide) (choices 1) [1,32,128] r11974 c11974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1035
  · exact u1036
  · exact u1037

def r11975 : Route 9 := (fun mask => (mask,id))

def c11975 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11975 : Upper (D 7) (R 7) [6,24,288,65,130,128] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,130,128] 13 (by decide) (choices 1) [1,32] r11975 c11975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1038
  · exact u1039

def b11976 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(1,5),(2,0),(3,5),(4,0)], upper := (rows 7 26 292 73 176 33 194 194 450), lower := (rows 7 26 292 73 176 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 48 32 67 131 259), good := (rows 454 474 308 456 180 500 64 128 256) },{ target := 5, region := (rows 1 18 4 41 16 0 83 147 275), good := (rows 463 474 268 457 474 457 64 128 256) }] }

theorem u11976 : Upper (D 7) (R 7) [6,24,288,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11977 : Route 9 := (fun mask => (mask,id))

def c11977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11977 : Upper (D 7) (R 7) [6,24,288,65,160,2] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,160,2] 13 (by decide) (choices 1) [1,128] r11977 c11977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1040
  · exact u1041

def r11978 : Route 9 := (fun mask => (mask,id))

def c11978 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11978 : Upper (D 7) (R 7) [6,24,288,65,160,64] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,160,64] 13 (by decide) (choices 1) [1,2,128] r11978 c11978
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1042
  · exact u1043
  · exact u1044

def b11979 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 292 73 176 160 67 195 323), lower := (rows 7 26 292 73 176 160 64 128 256), losses := [] }

theorem u11979 : Upper (D 7) (R 7) [6,24,288,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11980 : Route 9 := (fun mask => (mask,id))

def c11980 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11980 : Upper (D 7) (R 7) [6,24,288,65,192,1] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,192,1] 13 (by decide) (choices 1) [2,32,128] r11980 c11980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1045
  · exact u1046
  · exact u1047

def r11981 : Route 9 := (fun mask => (mask,id))

def c11981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11981 : Upper (D 7) (R 7) [6,24,288,65,192,2] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,192,2] 13 (by decide) (choices 1) [1,32,128] r11981 c11981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1048
  · exact u1049
  · exact u1050

def r11982 : Route 9 := (fun mask => (mask,id))

def c11982 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u11982 : Upper (D 7) (R 7) [6,24,288,65,192,128] 13 := by
  apply FastRouting.sound _ _ [6,24,288,65,192,128] 13 (by decide) (choices 1) [1,2,32] r11982 c11982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1051
  · exact u1052
  · exact u1053

def b11983 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,5),(2,1),(3,5),(4,1)], upper := (rows 7 26 292 74 176 33 193 193 449), lower := (rows 7 26 292 74 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 25 16 0 97 161 289), good := (rows 463 26 452 74 474 457 64 128 256) }] }

theorem u11983 : Upper (D 7) (R 7) [6,24,288,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11984 : Route 9 := (fun mask => (mask,id))

def c11984 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11984 : Upper (D 7) (R 7) [6,24,288,66,160,64] 13 := by
  apply FastRouting.sound _ _ [6,24,288,66,160,64] 13 (by decide) (choices 1) [1,128] r11984 c11984
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1054
  · exact u1055

def b11985 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 292 74 176 160 65 193 321), lower := (rows 7 26 292 74 176 160 64 128 256), losses := [] }

theorem u11985 : Upper (D 7) (R 7) [6,24,288,66,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11986 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,5)], upper := (rows 7 26 292 104 208 33 195 131 387), lower := (rows 7 26 292 104 208 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 49 0 65 129 257), good := (rows 471 26 276 90 208 465 64 128 256) }] }

theorem u11986 : Upper (D 7) (R 7) [6,24,288,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11987 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 26 292 104 208 34 193 129 385), lower := (rows 7 26 292 104 208 34 64 128 256), losses := [] }

theorem u11987 : Upper (D 7) (R 7) [6,24,288,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11988 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 4, region := 42, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,0)], upper := (rows 7 26 292 104 208 160 67 131 259), lower := (rows 7 26 292 104 208 160 64 128 256), losses := [] }

theorem u11988 : Upper (D 7) (R 7) [6,24,288,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11989 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 13 88 146 96 480 416 416), lower := (rows 7 35 13 88 146 96 64 128 256), losses := [] }

theorem u11989 : Upper (D 7) (R 7) [6,33,9,80,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11990 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(0,6),(3,0),(3,1),(4,0)], upper := (rows 7 35 13 88 146 160 352 480 352), lower := (rows 7 35 13 88 146 160 64 128 256), losses := [{ target := 6, region := (rows 13 10 12 8 16 176 0 128 256), good := (rows 7 35 15 63 178 160 0 160 256) }] }

theorem u11990 : Upper (D 7) (R 7) [6,33,9,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11991 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 13 88 146 288 224 224 480), lower := (rows 7 35 13 88 146 288 64 128 256), losses := [] }

theorem u11991 : Upper (D 7) (R 7) [6,33,9,80,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11991 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11992 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 88 176 34 448 448 448), lower := (rows 7 35 13 88 176 34 64 128 256), losses := [] }

theorem u11992 : Upper (D 7) (R 7) [6,33,9,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11993 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 13 88 176 96 450 386 386), lower := (rows 7 35 13 88 176 96 64 128 256), losses := [] }

theorem u11993 : Upper (D 7) (R 7) [6,33,9,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11994 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 13 88 176 160 322 450 322), lower := (rows 7 35 13 88 176 160 64 128 256), losses := [] }

theorem u11994 : Upper (D 7) (R 7) [6,33,9,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11995 : Route 9 := (fun mask => (mask,id))

def c11995 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11995 : Upper (D 7) (R 7) [6,33,9,80,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,9,80,160,256] 13 (by decide) (choices 1) [2,128] r11995 c11995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1056
  · exact u1057

def b11996 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 13 88 274 96 224 160 416), lower := (rows 7 35 13 88 274 96 64 128 256), losses := [] }

theorem u11996 : Upper (D 7) (R 7) [6,33,9,80,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11997 : Route 9 := (fun mask => (mask,id))

def c11997 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u11997 : Upper (D 7) (R 7) [6,33,9,80,258,128] 13 := by
  apply FastRouting.sound _ _ [6,33,9,80,258,128] 13 (by decide) (choices 1) [32,128] r11997 c11997
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1058
  · exact u1059

def b11998 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 39, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 13 88 304 34 192 192 448), lower := (rows 7 35 13 88 304 34 64 128 256), losses := [] }

theorem u11998 : Upper (D 7) (R 7) [6,33,9,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11999 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 13 88 304 96 194 130 386), lower := (rows 7 35 13 88 304 96 64 128 256), losses := [] }

theorem u11999 : Upper (D 7) (R 7) [6,33,9,80,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11999
end Delivery.IrregularNine14.P07
