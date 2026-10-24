import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0011
import IrregularNine14P07C0012

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8940 : Route 9 := (fun mask => (mask,id))

def c8940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8940 : Upper (D 7) (R 7) [36,192,320,3,160,2,1] 13 := by
  apply FastRouting.sound _ _ [36,192,320,3,160,2,1] 13 (by decide) (choices 1) [8,16] r8940 c8940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u710
  · exact u711

def b8941 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 194 324 11 176 34 72 145 273), lower := (rows 37 194 324 11 176 34 72 128 256), losses := [] }

theorem u8941 : Upper (D 7) (R 7) [36,192,320,3,160,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8941 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8942 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 324 11 176 34 80 137 265), lower := (rows 37 194 324 11 176 34 80 128 256), losses := [] }

theorem u8942 : Upper (D 7) (R 7) [36,192,320,3,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8942 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8943 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 176, targets := 65 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 37 194 324 11 176 40 65 146 274), lower := (rows 37 194 324 11 176 40 65 128 256), losses := [{ target := 0, region := (rows 0 70 70 8 57 40 64 201 329), good := (rows 438 454 454 446 176 440 470 128 256) }] }

theorem u8943 : Upper (D 7) (R 7) [36,192,320,3,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8943 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8944 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 37 194 324 11 176 40 66 145 273), lower := (rows 37 194 324 11 176 40 66 128 256), losses := [] }

theorem u8944 : Upper (D 7) (R 7) [36,192,320,3,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8944 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8945 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 324 11 176 40 80 131 259), lower := (rows 37 194 324 11 176 40 80 128 256), losses := [] }

theorem u8945 : Upper (D 7) (R 7) [36,192,320,3,160,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8945 [(5,3),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8946 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 453, targets := 2 },{ cop := 6, region := 422, targets := 1 }], pairs := [(0,1),(1,0),(2,0),(2,1)], upper := (rows 37 194 324 25 26 34 65 160 416), lower := (rows 37 194 324 25 26 34 65 128 256), losses := [] }

theorem u8946 : Upper (D 7) (R 7) [36,192,320,17,10,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8946 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8947 : Route 9 := (fun mask => (mask,id))

def c8947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8947 : Upper (D 7) (R 7) [36,192,320,17,10,2,32] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,10,2,32] 13 (by decide) (choices 1) [1] r8947 c8947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u712

def b8948 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 324 25 26 34 192 161 289), lower := (rows 37 194 324 25 26 34 192 128 256), losses := [] }

theorem u8948 : Upper (D 7) (R 7) [36,192,320,17,10,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8948 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8949 : Route 9 := (fun mask => (mask,id))

def c8949 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8949 : Upper (D 7) (R 7) [36,192,320,17,10,128,1] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,10,128,1] 13 (by decide) (choices 1) [2,32] r8949 c8949
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u713
  · exact u714

def b8950 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 293, targets := 2 },{ cop := 2, region := 161, targets := 64 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(1,0),(2,1)], upper := (rows 37 194 324 25 26 160 66 161 289), lower := (rows 37 194 324 25 26 160 66 128 256), losses := [] }

theorem u8950 : Upper (D 7) (R 7) [36,192,320,17,10,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8950 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8951 : Route 9 := (fun mask => (mask,id))

def c8951 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8951 : Upper (D 7) (R 7) [36,192,320,17,10,128,32] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,10,128,32] 13 (by decide) (choices 1) [1,2] r8951 c8951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u715
  · exact u716

def b8952 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 324 25 50 40 65 130 386), lower := (rows 37 194 324 25 50 40 65 128 256), losses := [] }

theorem u8952 : Upper (D 7) (R 7) [36,192,320,17,34,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8952 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8953 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 7, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 37 194 324 25 50 40 66 129 385), lower := (rows 37 194 324 25 50 40 66 128 256), losses := [] }

theorem u8953 : Upper (D 7) (R 7) [36,192,320,17,34,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8953 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8954 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 324 25 50 40 192 131 259), lower := (rows 37 194 324 25 50 40 192 128 256), losses := [] }

theorem u8954 : Upper (D 7) (R 7) [36,192,320,17,34,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8954 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8955 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 293, targets := 128 },{ cop := 6, region := 422, targets := 1 }], pairs := [(0,7),(1,0),(2,0),(2,7)], upper := (rows 37 194 324 25 152 34 65 162 290), lower := (rows 37 194 324 25 152 34 65 128 256), losses := [] }

theorem u8955 : Upper (D 7) (R 7) [36,192,320,17,136,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8956 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 324 25 152 34 66 161 289), lower := (rows 37 194 324 25 152 34 66 128 256), losses := [] }

theorem u8956 : Upper (D 7) (R 7) [36,192,320,17,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8957 : Route 9 := (fun mask => (mask,id))

def c8957 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8957 : Upper (D 7) (R 7) [36,192,320,17,136,2,32] 13 := by
  apply FastRouting.sound _ _ [36,192,320,17,136,2,32] 13 (by decide) (choices 1) [1,2] r8957 c8957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u717
  · exact u718

def b8958 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 390, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 194 324 25 176 40 65 130 258), lower := (rows 37 194 324 25 176 40 65 128 256), losses := [] }

theorem u8958 : Upper (D 7) (R 7) [36,192,320,17,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8958 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8959 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 37 194 324 25 176 40 66 131 259), lower := (rows 37 194 324 25 176 40 66 128 256), losses := [] }

theorem u8959 : Upper (D 7) (R 7) [36,192,320,17,160,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8959 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8960 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 4, region := 74, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,5)], upper := (rows 37 194 324 26 145 34 65 168 296), lower := (rows 37 194 324 26 145 34 65 128 256), losses := [] }

theorem u8960 : Upper (D 7) (R 7) [36,192,320,18,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8960 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8961 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 1, region := 293, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 37 194 324 26 145 34 72 161 289), lower := (rows 37 194 324 26 145 34 72 128 256), losses := [] }

theorem u8961 : Upper (D 7) (R 7) [36,192,320,18,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8961 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8962 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 194 324 26 145 34 96 137 265), lower := (rows 37 194 324 26 145 34 96 128 256), losses := [] }

theorem u8962 : Upper (D 7) (R 7) [36,192,320,18,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8963 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 4, region := 66, targets := 32 }], pairs := [(0,7),(1,5),(2,7)], upper := (rows 37 194 324 26 145 40 65 162 290), lower := (rows 37 194 324 26 145 40 65 128 256), losses := [] }

theorem u8963 : Upper (D 7) (R 7) [36,192,320,18,129,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8963 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8964 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 3, region := 357, targets := 128 }], pairs := [(0,7),(4,1),(4,6)], upper := (rows 37 194 324 26 145 40 66 161 289), lower := (rows 37 194 324 26 145 40 66 128 256), losses := [] }

theorem u8964 : Upper (D 7) (R 7) [36,192,320,18,129,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8964 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8965 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 194 324 26 145 40 96 131 259), lower := (rows 37 194 324 26 145 40 96 128 256), losses := [] }

theorem u8965 : Upper (D 7) (R 7) [36,192,320,18,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8965 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8966 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 324 42 145 33 66 152 280), lower := (rows 37 194 324 42 145 33 66 128 256), losses := [] }

theorem u8966 : Upper (D 7) (R 7) [36,192,320,34,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8967 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 194 324 42 145 33 72 146 274), lower := (rows 37 194 324 42 145 33 72 128 256), losses := [] }

theorem u8967 : Upper (D 7) (R 7) [36,192,320,34,129,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8967 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8968 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 324 42 145 33 80 138 266), lower := (rows 37 194 324 42 145 33 80 128 256), losses := [] }

theorem u8968 : Upper (D 7) (R 7) [36,192,320,34,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8968 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8969 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 325, targets := 128 },{ cop := 4, region := 66, targets := 32 }], pairs := [(0,7),(1,5),(2,7)], upper := (rows 37 194 324 42 145 48 65 138 266), lower := (rows 37 194 324 42 145 48 65 128 256), losses := [] }

theorem u8969 : Upper (D 7) (R 7) [36,192,320,34,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8969 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8970 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 325, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 194 324 42 145 48 66 137 265), lower := (rows 37 194 324 42 145 48 66 128 256), losses := [] }

theorem u8970 : Upper (D 7) (R 7) [36,192,320,34,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8970 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8971 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 325, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 324 42 145 48 72 131 259), lower := (rows 37 194 324 42 145 48 72 128 256), losses := [] }

theorem u8971 : Upper (D 7) (R 7) [36,192,320,34,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8971 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8972 : PairBound 9 := { available := 18, camps := [{ cop := 8, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 324 42 152 33 65 146 274), lower := (rows 37 194 324 42 152 33 65 128 256), losses := [] }

theorem u8972 : Upper (D 7) (R 7) [36,192,320,34,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8972 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8973 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 194 324 42 152 33 66 145 273), lower := (rows 37 194 324 42 152 33 66 128 256), losses := [] }

theorem u8973 : Upper (D 7) (R 7) [36,192,320,34,136,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8974 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 324 42 152 33 80 131 259), lower := (rows 37 194 324 42 152 33 80 128 256), losses := [] }

theorem u8974 : Upper (D 7) (R 7) [36,192,320,34,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8974 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8975 : Route 9 := (fun mask => (mask,id))

def c8975 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8975 : Upper (D 7) (R 7) [36,192,320,48,129,2,1] 13 := by
  apply FastRouting.sound _ _ [36,192,320,48,129,2,1] 13 (by decide) (choices 1) [2,8] r8975 c8975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u719
  · exact u720

def b8976 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 152, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 194 324 56 145 34 66 137 265), lower := (rows 37 194 324 56 145 34 66 128 256), losses := [] }

theorem u8976 : Upper (D 7) (R 7) [36,192,320,48,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8977 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 293, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 194 324 56 145 34 72 131 259), lower := (rows 37 194 324 56 145 34 72 128 256), losses := [] }

theorem u8977 : Upper (D 7) (R 7) [36,192,320,48,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8977 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8978 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 0, region := 450, targets := 32 },{ cop := 6, region := 176, targets := 2 }], pairs := [(1,5),(3,0),(4,0),(4,1)], upper := (rows 37 259 13 26 112 160 66 192 448), lower := (rows 37 259 13 26 112 160 66 128 256), losses := [] }

theorem u8978 : Upper (D 7) (R 7) [36,257,9,18,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8979 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 13 26 112 160 192 194 322), lower := (rows 37 259 13 26 112 160 192 128 256), losses := [] }

theorem u8979 : Upper (D 7) (R 7) [36,257,9,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8980 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 259 13 74 50 160 80 192 448), lower := (rows 37 259 13 74 50 160 80 128 256), losses := [] }

theorem u8980 : Upper (D 7) (R 7) [36,257,9,66,34,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8980 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8981 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 4, region := 200, targets := 32 }], pairs := [(0,1),(3,0),(3,5),(4,0)], upper := (rows 37 259 13 74 50 160 192 208 336), lower := (rows 37 259 13 74 50 160 192 128 256), losses := [{ target := 1, region := (rows 9 0 12 8 16 240 240 144 272), good := (rows 101 257 13 109 496 224 224 224 256) }] }

theorem u8981 : Upper (D 7) (R 7) [36,257,9,66,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8982 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 37 259 13 74 112 160 66 144 400), lower := (rows 37 259 13 74 112 160 66 128 256), losses := [] }

theorem u8982 : Upper (D 7) (R 7) [36,257,9,66,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8983 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 259 13 74 112 160 80 130 386), lower := (rows 37 259 13 74 112 160 80 128 256), losses := [] }

theorem u8983 : Upper (D 7) (R 7) [36,257,9,66,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8983 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8984 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 259 13 74 112 160 192 146 274), lower := (rows 37 259 13 74 112 160 192 128 256), losses := [] }

theorem u8984 : Upper (D 7) (R 7) [36,257,9,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8985 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 259 13 74 146 48 96 192 448), lower := (rows 37 259 13 74 146 48 96 128 256), losses := [] }

theorem u8985 : Upper (D 7) (R 7) [36,257,9,66,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8985 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8986 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 4, region := 72, targets := 32 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 37 259 13 74 146 48 192 224 352), lower := (rows 37 259 13 74 146 48 192 128 256), losses := [] }

theorem u8986 : Upper (D 7) (R 7) [36,257,9,66,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8986 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8987 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 165, targets := 2 }], pairs := [(0,1),(3,0),(4,0)], upper := (rows 37 259 13 74 146 160 80 224 352), lower := (rows 37 259 13 74 146 160 80 128 256), losses := [] }

theorem u8987 : Upper (D 7) (R 7) [36,257,9,66,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8987 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8988 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 144, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 37 259 13 74 146 160 96 208 336), lower := (rows 37 259 13 74 146 160 96 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 28 0 64 136 264), good := (rows 23 259 415 474 146 128 64 128 256) }] }

theorem u8988 : Upper (D 7) (R 7) [36,257,9,66,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8989 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 76, targets := 160 }], pairs := [(2,5),(2,7),(3,5),(3,7)], upper := (rows 37 259 13 74 208 160 66 176 304), lower := (rows 37 259 13 74 208 160 66 128 256), losses := [] }

theorem u8989 : Upper (D 7) (R 7) [36,257,9,66,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8990 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 259 13 74 208 160 80 162 290), lower := (rows 37 259 13 74 208 160 80 128 256), losses := [] }

theorem u8990 : Upper (D 7) (R 7) [36,257,9,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8990 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8991 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 3, region := 144, targets := 32 },{ cop := 5, region := 80, targets := 2 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 37 259 13 74 208 160 96 146 274), lower := (rows 37 259 13 74 208 160 96 128 256), losses := [] }

theorem u8991 : Upper (D 7) (R 7) [36,257,9,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8992 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 259 13 200 82 34 80 160 416), lower := (rows 37 259 13 200 82 34 80 128 256), losses := [] }

theorem u8992 : Upper (D 7) (R 7) [36,257,9,192,66,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8992 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8993 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 248, targets := 1 },{ cop := 4, region := 136, targets := 34 }], pairs := [(3,0),(3,1),(3,5),(4,0)], upper := (rows 37 259 13 200 82 34 96 144 400), lower := (rows 37 259 13 200 82 34 96 128 256), losses := [] }

theorem u8993 : Upper (D 7) (R 7) [36,257,9,192,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8994 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 259 13 200 82 34 192 176 304), lower := (rows 37 259 13 200 82 34 192 128 256), losses := [] }

theorem u8994 : Upper (D 7) (R 7) [36,257,9,192,66,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8995 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 141, targets := 2 },{ cop := 1, region := 248, targets := 1 }], pairs := [(0,1),(2,1),(3,0),(3,1)], upper := (rows 37 259 13 200 112 34 66 144 400), lower := (rows 37 259 13 200 112 34 66 128 256), losses := [] }

theorem u8995 : Upper (D 7) (R 7) [36,257,9,192,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8996 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 37 259 13 200 112 34 80 130 386), lower := (rows 37 259 13 200 112 34 80 128 256), losses := [] }

theorem u8996 : Upper (D 7) (R 7) [36,257,9,192,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8996 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8997 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 259 13 200 112 34 192 146 274), lower := (rows 37 259 13 200 112 34 192 128 256), losses := [] }

theorem u8997 : Upper (D 7) (R 7) [36,257,9,192,96,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8998 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 240, targets := 1 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(1,5),(2,5),(4,0)], upper := (rows 37 259 14 25 82 160 96 192 448), lower := (rows 37 259 14 25 82 160 96 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 16 0 64 208 336), good := (rows 5 259 14 415 466 128 448 128 256) }] }

theorem u8998 : Upper (D 7) (R 7) [36,257,10,17,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8999 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 240, targets := 1 },{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,6),(2,6),(4,0)], upper := (rows 37 259 14 25 82 160 192 224 352), lower := (rows 37 259 14 25 82 160 192 128 256), losses := [{ target := 6, region := (rows 17 2 20 24 16 224 0 128 256), good := (rows 37 259 14 29 63 160 160 160 256) }] }

theorem u8999 : Upper (D 7) (R 7) [36,257,10,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8999
end Delivery.IrregularNine14.P07
