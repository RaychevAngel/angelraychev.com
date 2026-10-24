import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0183
import IrregularNine14P07C0184

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b29040 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 44 11 146 96 209 145 401), lower := (rows 97 262 44 11 146 96 64 128 256), losses := [] }

theorem u29040 : Upper (D 7) (R 7) [96,260,40,3,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29041 : Route 9 := (fun mask => (mask,id))

def c29041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29041 : Upper (D 7) (R 7) [96,260,40,3,130,128] 13 := by
  apply FastRouting.sound _ _ [96,260,40,3,130,128] 13 (by decide) (choices 1) [1,16] r29041 c29041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11027
  · exact u11028

def b29042 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 44 11 208 33 210 146 402), lower := (rows 97 262 44 11 208 33 64 128 256), losses := [] }

theorem u29042 : Upper (D 7) (R 7) [96,260,40,3,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29043 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 36, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,0),(2,6),(2,7),(4,1)], upper := (rows 97 262 44 11 208 34 209 145 401), lower := (rows 97 262 44 11 208 34 64 128 256), losses := [] }

theorem u29043 : Upper (D 7) (R 7) [96,260,40,3,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29044 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 44 11 208 48 195 131 387), lower := (rows 97 262 44 11 208 48 64 128 256), losses := [] }

theorem u29044 : Upper (D 7) (R 7) [96,260,40,3,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29044 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29045 : Route 9 := (fun mask => (mask,id))

def c29045 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29045 : Upper (D 7) (R 7) [96,260,40,3,192,128] 13 := by
  apply FastRouting.sound _ _ [96,260,40,3,192,128] 13 (by decide) (choices 1) [1,2,16] r29045 c29045
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11029
  · exact u11030
  · exact u11031

def b29046 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 44 25 82 33 194 130 386), lower := (rows 97 262 44 25 82 33 64 128 256), losses := [] }

theorem u29046 : Upper (D 7) (R 7) [96,260,40,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29047 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 45, targets := 128 },{ cop := 3, region := 422, targets := 64 }], pairs := [(0,7),(1,6),(2,7),(3,7)], upper := (rows 97 262 44 25 82 34 193 129 385), lower := (rows 97 262 44 25 82 34 64 128 256), losses := [] }

theorem u29047 : Upper (D 7) (R 7) [96,260,40,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29048 : Route 9 := (fun mask => (mask,id))

def c29048 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29048 : Upper (D 7) (R 7) [96,260,40,17,66,128] 13 := by
  apply FastRouting.sound _ _ [96,260,40,17,66,128] 13 (by decide) (choices 1) [1,2,128] r29048 c29048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11032
  · exact u11033
  · exact u11034

def b29049 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 44 25 146 33 194 194 450), lower := (rows 97 262 44 25 146 33 64 128 256), losses := [] }

theorem u29049 : Upper (D 7) (R 7) [96,260,40,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29049 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29050 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 193, targets := 2 }], pairs := [(0,1),(1,5),(2,0),(4,5)], upper := (rows 97 262 44 25 146 34 193 193 449), lower := (rows 97 262 44 25 146 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 50 64 128 256), good := (rows 96 294 44 60 178 34 64 128 256) },{ target := 5, region := (rows 1 6 4 8 20 0 73 137 265), good := (rows 449 278 478 473 146 2 64 128 256) }] }

theorem u29050 : Upper (D 7) (R 7) [96,260,40,17,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29051 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 44 25 146 96 195 131 387), lower := (rows 97 262 44 25 146 96 64 128 256), losses := [] }

theorem u29051 : Upper (D 7) (R 7) [96,260,40,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29052 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(2,1)], upper := (rows 97 262 44 25 146 160 67 195 323), lower := (rows 97 262 44 25 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 96 262 44 60 178 160 64 160 256) },{ target := 1, region := (rows 1 0 12 8 16 176 64 128 256), good := (rows 97 260 44 61 176 160 64 160 256) }] }

theorem u29052 : Upper (D 7) (R 7) [96,260,40,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29053 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 45, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 44 25 208 33 194 130 386), lower := (rows 97 262 44 25 208 33 64 128 256), losses := [] }

theorem u29053 : Upper (D 7) (R 7) [96,260,40,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29054 : Route 9 := (fun mask => (mask,id))

def c29054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29054 : Upper (D 7) (R 7) [96,260,40,17,192,2] 13 := by
  apply FastRouting.sound _ _ [96,260,40,17,192,2] 13 (by decide) (choices 1) [1,2,128] r29054 c29054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11035
  · exact u11036
  · exact u11037

def b29055 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 45, targets := 2 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 97 262 44 25 208 160 67 131 259), lower := (rows 97 262 44 25 208 160 64 128 256), losses := [] }

theorem u29055 : Upper (D 7) (R 7) [96,260,40,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29056 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(1,5)], upper := (rows 97 262 44 26 145 33 194 194 450), lower := (rows 97 262 44 26 145 33 64 128 256), losses := [] }

theorem u29056 : Upper (D 7) (R 7) [96,260,40,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29057 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 36, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,0),(2,6),(2,7),(4,1)], upper := (rows 97 262 44 26 145 34 193 193 449), lower := (rows 97 262 44 26 145 34 64 128 256), losses := [] }

theorem u29057 : Upper (D 7) (R 7) [96,260,40,18,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29058 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 44 26 145 96 195 131 387), lower := (rows 97 262 44 26 145 96 64 128 256), losses := [] }

theorem u29058 : Upper (D 7) (R 7) [96,260,40,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29059 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(2,0),(2,1)], upper := (rows 97 262 44 26 145 160 67 195 323), lower := (rows 97 262 44 26 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 96 262 44 62 176 160 64 160 256) },{ target := 1, region := (rows 1 0 12 8 16 176 64 128 256), good := (rows 97 260 44 60 177 160 64 160 256) }] }

theorem u29059 : Upper (D 7) (R 7) [96,260,40,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29060 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 44 26 208 33 195 131 387), lower := (rows 97 262 44 26 208 33 64 128 256), losses := [{ target := 1, region := (rows 81 0 12 8 16 121 64 128 256), good := (rows 97 260 44 61 241 33 97 128 256) },{ target := 7, region := (rows 81 2 12 8 16 121 64 0 256), good := (rows 97 262 44 63 113 33 97 0 256) }] }

theorem u29060 : Upper (D 7) (R 7) [96,260,40,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29061 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 36, targets := 193 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,0),(2,6),(2,7),(4,1)], upper := (rows 97 262 44 26 208 34 193 129 385), lower := (rows 97 262 44 26 208 34 64 128 256), losses := [] }

theorem u29061 : Upper (D 7) (R 7) [96,260,40,18,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29062 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 323, targets := 128 },{ cop := 4, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(1,7),(2,0)], upper := (rows 97 262 44 26 208 160 67 131 259), lower := (rows 97 262 44 26 208 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 96 262 44 62 240 160 64 160 256) }] }

theorem u29062 : Upper (D 7) (R 7) [96,260,40,18,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29063 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 53, targets := 128 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 97 262 44 74 19 33 208 144 400), lower := (rows 97 262 44 74 19 33 64 128 256), losses := [] }

theorem u29063 : Upper (D 7) (R 7) [96,260,40,66,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29064 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 53, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 262 44 74 19 48 193 129 385), lower := (rows 97 262 44 74 19 48 64 128 256), losses := [] }

theorem u29064 : Upper (D 7) (R 7) [96,260,40,66,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29064 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29065 : Route 9 := (fun mask => (mask,id))

def c29065 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29065 : Upper (D 7) (R 7) [96,260,40,66,3,128] 13 := by
  apply FastRouting.sound _ _ [96,260,40,66,3,128] 13 (by decide) (choices 1) [1,16,128] r29065 c29065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11038
  · exact u11039
  · exact u11040

def b29066 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 44 74 145 33 210 146 402), lower := (rows 97 262 44 74 145 33 64 128 256), losses := [] }

theorem u29066 : Upper (D 7) (R 7) [96,260,40,66,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29067 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 144, targets := 34 },{ cop := 3, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(4,1),(4,5)], upper := (rows 97 262 44 74 145 34 209 145 401), lower := (rows 97 262 44 74 145 34 64 128 256), losses := [] }

theorem u29067 : Upper (D 7) (R 7) [96,260,40,66,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29068 : Route 9 := (fun mask => (mask,id))

def c29068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29068 : Upper (D 7) (R 7) [96,260,40,66,129,16] 13 := by
  apply FastRouting.sound _ _ [96,260,40,66,129,16] 13 (by decide) (choices 1) [1,2,128] r29068 c29068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11041
  · exact u11042
  · exact u11043

def r29069 : Route 9 := (fun mask => (mask,id))

def c29069 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29069 : Upper (D 7) (R 7) [96,260,40,66,129,128] 13 := by
  apply FastRouting.sound _ _ [96,260,40,66,129,128] 13 (by decide) (choices 1) [1,2,16] r29069 c29069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11044
  · exact u11045
  · exact u11046

def b29070 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 44 74 146 33 209 145 401), lower := (rows 97 262 44 74 146 33 64 128 256), losses := [] }

theorem u29070 : Upper (D 7) (R 7) [96,260,40,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29071 : Route 9 := (fun mask => (mask,id))

def c29071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29071 : Upper (D 7) (R 7) [96,260,40,66,130,16] 13 := by
  apply FastRouting.sound _ _ [96,260,40,66,130,16] 13 (by decide) (choices 1) [1,128] r29071 c29071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11047
  · exact u11048

def r29072 : Route 9 := (fun mask => (mask,id))

def c29072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29072 : Upper (D 7) (R 7) [96,260,40,66,130,128] 13 := by
  apply FastRouting.sound _ _ [96,260,40,66,130,128] 13 (by decide) (choices 1) [1,16] r29072 c29072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11049
  · exact u11050

def b29073 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 44 88 19 33 194 130 386), lower := (rows 97 262 44 88 19 33 64 128 256), losses := [] }

theorem u29073 : Upper (D 7) (R 7) [96,260,40,80,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29074 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 200, targets := 34 },{ cop := 2, region := 193, targets := 2 }], pairs := [(0,1),(2,0),(3,1),(3,5)], upper := (rows 97 262 44 88 19 34 193 129 385), lower := (rows 97 262 44 88 19 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 50 64 128 256), good := (rows 96 294 44 124 50 34 64 128 256) }] }

theorem u29074 : Upper (D 7) (R 7) [96,260,40,80,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29075 : Route 9 := (fun mask => (mask,id))

def c29075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29075 : Upper (D 7) (R 7) [96,260,40,80,3,128] 13 := by
  apply FastRouting.sound _ _ [96,260,40,80,3,128] 13 (by decide) (choices 1) [1,2,128] r29075 c29075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11051
  · exact u11052
  · exact u11053

def b29076 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 44 88 145 33 194 130 386), lower := (rows 97 262 44 88 145 33 64 128 256), losses := [] }

theorem u29076 : Upper (D 7) (R 7) [96,260,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29077 : Route 9 := (fun mask => (mask,id))

def c29077 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29077 : Upper (D 7) (R 7) [96,260,40,80,129,2] 13 := by
  apply FastRouting.sound _ _ [96,260,40,80,129,2] 13 (by decide) (choices 1) [1,2,128] r29077 c29077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11054
  · exact u11055
  · exact u11056

def b29078 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(2,0)], upper := (rows 97 262 44 88 145 160 67 131 259), lower := (rows 97 262 44 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 96 262 44 124 176 160 64 160 256) },{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 97 260 45 125 177 160 64 160 256) }] }

theorem u29078 : Upper (D 7) (R 7) [96,260,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29079 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 97 262 44 88 146 33 195 131 387), lower := (rows 97 262 44 88 146 33 64 128 256), losses := [] }

theorem u29079 : Upper (D 7) (R 7) [96,260,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29080 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 193, targets := 2 }], pairs := [(0,1),(2,0),(2,6),(3,1)], upper := (rows 97 262 44 88 146 34 193 129 385), lower := (rows 97 262 44 88 146 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 50 64 128 256), good := (rows 96 294 44 124 178 34 64 128 256) },{ target := 1, region := (rows 37 0 4 24 16 32 103 167 295), good := (rows 481 453 493 88 472 481 64 128 256) },{ target := 6, region := (rows 1 2 12 8 16 50 0 129 257), good := (rows 417 294 44 60 178 34 0 128 256) }] }

theorem u29080 : Upper (D 7) (R 7) [96,260,40,80,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29081 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(2,0)], upper := (rows 97 262 44 88 146 160 67 131 259), lower := (rows 97 262 44 88 146 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 176 64 128 256), good := (rows 96 262 44 124 178 160 64 160 256) },{ target := 1, region := (rows 9 0 12 8 16 176 64 128 256), good := (rows 97 260 45 125 176 160 64 160 256) }] }

theorem u29081 : Upper (D 7) (R 7) [96,260,40,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29082 : Route 9 := (fun mask => (mask,id))

def c29082 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29082 : Upper (D 7) (R 7) [96,260,40,129,3,2] 13 := by
  apply FastRouting.sound _ _ [96,260,40,129,3,2] 13 (by decide) (choices 1) [16,128] r29082 c29082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11057
  · exact u11058

def b29083 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 450, targets := 33 },{ cop := 4, region := 200, targets := 32 }], pairs := [(1,0),(1,5),(3,5)], upper := (rows 97 262 44 137 19 48 194 194 450), lower := (rows 97 262 44 137 19 48 64 128 256), losses := [] }

theorem u29083 : Upper (D 7) (R 7) [96,260,40,129,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29083 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29084 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 44 137 19 96 210 146 402), lower := (rows 97 262 44 137 19 96 64 128 256), losses := [] }

theorem u29084 : Upper (D 7) (R 7) [96,260,40,129,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29085 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 262 44 137 19 160 82 210 338), lower := (rows 97 262 44 137 19 160 64 128 256), losses := [] }

theorem u29085 : Upper (D 7) (R 7) [96,260,40,129,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29086 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 44 137 82 33 210 146 402), lower := (rows 97 262 44 137 82 33 64 128 256), losses := [] }

theorem u29086 : Upper (D 7) (R 7) [96,260,40,129,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29087 : Route 9 := (fun mask => (mask,id))

def c29087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29087 : Upper (D 7) (R 7) [96,260,40,129,66,2] 13 := by
  apply FastRouting.sound _ _ [96,260,40,129,66,2] 13 (by decide) (choices 1) [1,16,128] r29087 c29087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11059
  · exact u11060
  · exact u11061

def b29088 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 44 137 82 48 195 131 387), lower := (rows 97 262 44 137 82 48 64 128 256), losses := [] }

theorem u29088 : Upper (D 7) (R 7) [96,260,40,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29088 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29089 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 97 262 44 137 82 160 83 147 275), lower := (rows 97 262 44 137 82 160 64 128 256), losses := [] }

theorem u29089 : Upper (D 7) (R 7) [96,260,40,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29089 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29090 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 44 137 146 33 82 210 338), lower := (rows 97 262 44 137 146 33 64 128 256), losses := [] }

theorem u29090 : Upper (D 7) (R 7) [96,260,40,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29091 : Route 9 := (fun mask => (mask,id))

def c29091 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29091 : Upper (D 7) (R 7) [96,260,40,129,130,2] 13 := by
  apply FastRouting.sound _ _ [96,260,40,129,130,2] 13 (by decide) (choices 1) [1,16] r29091 c29091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11062
  · exact u11063

def r29092 : Route 9 := (fun mask => (mask,id))

def c29092 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29092 : Upper (D 7) (R 7) [96,260,40,129,130,16] 13 := by
  apply FastRouting.sound _ _ [96,260,40,129,130,16] 13 (by decide) (choices 1) [1,2] r29092 c29092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11064
  · exact u11065

def b29093 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 44 137 146 96 83 147 275), lower := (rows 97 262 44 137 146 96 64 128 256), losses := [] }

theorem u29093 : Upper (D 7) (R 7) [96,260,40,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29094 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 97 262 44 137 208 33 82 146 274), lower := (rows 97 262 44 137 208 33 64 128 256), losses := [] }

theorem u29094 : Upper (D 7) (R 7) [96,260,40,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29095 : Route 9 := (fun mask => (mask,id))

def c29095 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u29095 : Upper (D 7) (R 7) [96,260,40,129,192,2] 13 := by
  apply FastRouting.sound _ _ [96,260,40,129,192,2] 13 (by decide) (choices 1) [1,2,16] r29095 c29095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u11066
  · exact u11067
  · exact u11068

def b29096 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 262 44 137 208 48 67 131 259), lower := (rows 97 262 44 137 208 48 64 128 256), losses := [] }

theorem u29096 : Upper (D 7) (R 7) [96,260,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29096 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29097 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 200, targets := 33 },{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(3,0),(3,5)], upper := (rows 97 262 44 138 19 33 208 208 464), lower := (rows 97 262 44 138 19 33 64 128 256), losses := [] }

theorem u29097 : Upper (D 7) (R 7) [96,260,40,130,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r29098 : Route 9 := (fun mask => (mask,id))

def c29098 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u29098 : Upper (D 7) (R 7) [96,260,40,130,3,16] 13 := by
  apply FastRouting.sound _ _ [96,260,40,130,3,16] 13 (by decide) (choices 1) [1,128] r29098 c29098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u11069
  · exact u11070

def b29099 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 262 44 138 19 96 209 145 401), lower := (rows 97 262 44 138 19 96 64 128 256), losses := [] }

theorem u29099 : Upper (D 7) (R 7) [96,260,40,130,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u29099
end Delivery.IrregularNine14.P07
