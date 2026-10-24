import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0154

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26040 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 0, region := 402, targets := 32 }], pairs := [(1,5),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 168 145 96 82 146 274), lower := (rows 37 259 76 168 145 96 64 128 256), losses := [] }

theorem u26040 : Upper (D 7) (R 7) [36,257,72,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26041 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 259 76 168 146 33 82 210 338), lower := (rows 37 259 76 168 146 33 64 128 256), losses := [] }

theorem u26041 : Upper (D 7) (R 7) [36,257,72,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26042 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 40, targets := 65 }], pairs := [(1,5),(3,0),(3,6),(4,5)], upper := (rows 37 259 76 168 146 34 81 209 337), lower := (rows 37 259 76 168 146 34 64 128 256), losses := [] }

theorem u26042 : Upper (D 7) (R 7) [36,257,72,160,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26043 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 76 168 146 48 67 195 323), lower := (rows 37 259 76 168 146 48 64 128 256), losses := [] }

theorem u26043 : Upper (D 7) (R 7) [36,257,72,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26043 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26044 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 0, region := 402, targets := 32 }], pairs := [(1,5),(1,6),(3,6),(4,6)], upper := (rows 37 259 76 168 146 96 83 147 275), lower := (rows 37 259 76 168 146 96 64 128 256), losses := [] }

theorem u26044 : Upper (D 7) (R 7) [36,257,72,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26045 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 466, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 259 76 168 208 33 82 146 274), lower := (rows 37 259 76 168 208 33 64 128 256), losses := [] }

theorem u26045 : Upper (D 7) (R 7) [36,257,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26046 : Route 9 := (fun mask => (mask,id))

def c26046 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26046 : Upper (D 7) (R 7) [36,257,72,160,192,2] 13 := by
  apply FastRouting.sound _ _ [36,257,72,160,192,2] 13 (by decide) (choices 1) [1,2,16] r26046 c26046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9244
  · exact u9245
  · exact u9246

def b26047 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 259 76 168 208 48 67 131 259), lower := (rows 37 259 76 168 208 48 64 128 256), losses := [] }

theorem u26047 : Upper (D 7) (R 7) [36,257,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26047 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26048 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 37 259 196 25 50 34 200 200 456), lower := (rows 37 259 196 25 50 34 64 128 256), losses := [] }

theorem u26048 : Upper (D 7) (R 7) [36,257,192,17,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26049 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6)], upper := (rows 37 259 196 25 50 40 194 194 450), lower := (rows 37 259 196 25 50 40 64 128 256), losses := [] }

theorem u26049 : Upper (D 7) (R 7) [36,257,192,17,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26049 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26050 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,6),(3,6),(4,6)], upper := (rows 37 259 196 25 50 96 202 138 394), lower := (rows 37 259 196 25 50 96 64 128 256), losses := [] }

theorem u26050 : Upper (D 7) (R 7) [36,257,192,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26051 : Route 9 := (fun mask => (mask,id))

def c26051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26051 : Upper (D 7) (R 7) [36,257,192,17,66,2] 13 := by
  apply FastRouting.sound _ _ [36,257,192,17,66,2] 13 (by decide) (choices 1) [8,32,128] r26051 c26051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9247
  · exact u9248
  · exact u9249

def r26052 : Route 9 := (fun mask => (mask,id))

def c26052 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26052 : Upper (D 7) (R 7) [36,257,192,17,66,8] 13 := by
  apply FastRouting.sound _ _ [36,257,192,17,66,8] 13 (by decide) (choices 1) [2,32,128] r26052 c26052
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9250
  · exact u9251
  · exact u9252

def b26053 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 25 82 160 106 170 298), lower := (rows 37 259 196 25 82 160 64 128 256), losses := [] }

theorem u26053 : Upper (D 7) (R 7) [36,257,192,17,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26054 : Route 9 := (fun mask => (mask,id))

def c26054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26054 : Upper (D 7) (R 7) [36,257,192,17,72,2] 13 := by
  apply FastRouting.sound _ _ [36,257,192,17,72,2] 13 (by decide) (choices 1) [2,32,128] r26054 c26054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9253
  · exact u9254
  · exact u9255

def b26055 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 25 88 160 98 162 290), lower := (rows 37 259 196 25 88 160 64 128 256), losses := [] }

theorem u26055 : Upper (D 7) (R 7) [36,257,192,17,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26056 : Route 9 := (fun mask => (mask,id))

def c26056 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26056 : Upper (D 7) (R 7) [36,257,192,17,96,2] 13 := by
  apply FastRouting.sound _ _ [36,257,192,17,96,2] 13 (by decide) (choices 1) [2,8,128] r26056 c26056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9256
  · exact u9257
  · exact u9258

def b26057 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 57, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 259 196 25 112 40 194 130 386), lower := (rows 37 259 196 25 112 40 64 128 256), losses := [] }

theorem u26057 : Upper (D 7) (R 7) [36,257,192,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26057 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26058 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 25 112 160 74 138 266), lower := (rows 37 259 196 25 112 160 64 128 256), losses := [] }

theorem u26058 : Upper (D 7) (R 7) [36,257,192,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26059 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 56, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 37 259 196 26 56 33 194 194 450), lower := (rows 37 259 196 26 56 33 64 128 256), losses := [] }

theorem u26059 : Upper (D 7) (R 7) [36,257,192,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26060 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 56, targets := 193 }], pairs := [(3,0),(3,6),(3,7),(4,0)], upper := (rows 37 259 196 26 56 34 193 193 449), lower := (rows 37 259 196 26 56 34 64 128 256), losses := [] }

theorem u26060 : Upper (D 7) (R 7) [36,257,192,18,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26061 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 410, targets := 64 },{ cop := 0, region := 386, targets := 32 }], pairs := [(1,5),(1,6),(3,6),(4,6)], upper := (rows 37 259 196 26 56 96 195 131 387), lower := (rows 37 259 196 26 56 96 64 128 256), losses := [] }

theorem u26061 : Upper (D 7) (R 7) [36,257,192,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26062 : Route 9 := (fun mask => (mask,id))

def c26062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u26062 : Upper (D 7) (R 7) [36,257,192,18,65,2] 13 := by
  apply FastRouting.sound _ _ [36,257,192,18,65,2] 13 (by decide) (choices 1) [8,32,128] r26062 c26062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9259
  · exact u9260
  · exact u9261

def b26063 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 426, targets := 64 },{ cop := 3, region := 228, targets := 1 }], pairs := [(1,6),(2,0),(3,6)], upper := (rows 37 259 196 26 81 40 226 162 418), lower := (rows 37 259 196 26 81 40 64 128 256), losses := [] }

theorem u26063 : Upper (D 7) (R 7) [36,257,192,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26063 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26064 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 26 81 160 106 170 298), lower := (rows 37 259 196 26 81 160 64 128 256), losses := [] }

theorem u26064 : Upper (D 7) (R 7) [36,257,192,18,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26065 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 130 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(1,6)], upper := (rows 37 259 196 26 88 33 226 162 418), lower := (rows 37 259 196 26 88 33 64 128 256), losses := [] }

theorem u26065 : Upper (D 7) (R 7) [36,257,192,18,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26065 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26066 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 5, region := 197, targets := 2 }], pairs := [(0,1),(0,6),(1,6),(2,1)], upper := (rows 37 259 196 26 88 34 225 161 417), lower := (rows 37 259 196 26 88 34 64 128 256), losses := [] }

theorem u26066 : Upper (D 7) (R 7) [36,257,192,18,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26067 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 26 88 160 99 163 291), lower := (rows 37 259 196 26 88 160 64 128 256), losses := [] }

theorem u26067 : Upper (D 7) (R 7) [36,257,192,18,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26068 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1),(4,7)], upper := (rows 37 259 196 26 112 33 202 138 394), lower := (rows 37 259 196 26 112 33 64 128 256), losses := [] }

theorem u26068 : Upper (D 7) (R 7) [36,257,192,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26069 : Route 9 := (fun mask => (mask,id))

def c26069 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26069 : Upper (D 7) (R 7) [36,257,192,18,96,2] 13 := by
  apply FastRouting.sound _ _ [36,257,192,18,96,2] 13 (by decide) (choices 1) [1,8,128] r26069 c26069
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9262
  · exact u9263
  · exact u9264

def b26070 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 37 259 196 26 112 40 195 131 387), lower := (rows 37 259 196 26 112 40 64 128 256), losses := [] }

theorem u26070 : Upper (D 7) (R 7) [36,257,192,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26070 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26071 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 26 112 160 75 139 267), lower := (rows 37 259 196 26 112 160 64 128 256), losses := [] }

theorem u26071 : Upper (D 7) (R 7) [36,257,192,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26072 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 259 196 42 81 34 216 152 408), lower := (rows 37 259 196 42 81 34 64 128 256), losses := [] }

theorem u26072 : Upper (D 7) (R 7) [36,257,192,34,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26073 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 259 196 42 81 40 210 146 402), lower := (rows 37 259 196 42 81 40 64 128 256), losses := [] }

theorem u26073 : Upper (D 7) (R 7) [36,257,192,34,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26073 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26074 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 49, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 37 259 196 42 81 48 202 138 394), lower := (rows 37 259 196 42 81 48 64 128 256), losses := [] }

theorem u26074 : Upper (D 7) (R 7) [36,257,192,34,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26074 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26075 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 42 81 160 90 154 282), lower := (rows 37 259 196 42 81 160 64 128 256), losses := [] }

theorem u26075 : Upper (D 7) (R 7) [36,257,192,34,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26076 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 259 196 42 82 33 216 152 408), lower := (rows 37 259 196 42 82 33 64 128 256), losses := [] }

theorem u26076 : Upper (D 7) (R 7) [36,257,192,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26077 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 259 196 42 82 40 209 145 401), lower := (rows 37 259 196 42 82 40 64 128 256), losses := [] }

theorem u26077 : Upper (D 7) (R 7) [36,257,192,34,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26077 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26078 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 40, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 37 259 196 42 82 48 201 137 393), lower := (rows 37 259 196 42 82 48 64 128 256), losses := [] }

theorem u26078 : Upper (D 7) (R 7) [36,257,192,34,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26078 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26079 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 42 82 160 89 153 281), lower := (rows 37 259 196 42 82 160 64 128 256), losses := [] }

theorem u26079 : Upper (D 7) (R 7) [36,257,192,34,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26080 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 212, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 259 196 42 88 33 210 146 402), lower := (rows 37 259 196 42 88 33 64 128 256), losses := [] }

theorem u26080 : Upper (D 7) (R 7) [36,257,192,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26081 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 40, targets := 193 },{ cop := 3, region := 213, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 259 196 42 88 34 209 145 401), lower := (rows 37 259 196 42 88 34 64 128 256), losses := [] }

theorem u26081 : Upper (D 7) (R 7) [36,257,192,34,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26082 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 0, region := 386, targets := 64 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 37 259 196 42 88 48 195 131 387), lower := (rows 37 259 196 42 88 48 64 128 256), losses := [] }

theorem u26082 : Upper (D 7) (R 7) [36,257,192,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26082 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26083 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 42 88 160 83 147 275), lower := (rows 37 259 196 42 88 160 64 128 256), losses := [] }

theorem u26083 : Upper (D 7) (R 7) [36,257,192,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26084 : Route 9 := (fun mask => (mask,id))

def c26084 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u26084 : Upper (D 7) (R 7) [36,257,192,48,65,2] 13 := by
  apply FastRouting.sound _ _ [36,257,192,48,65,2] 13 (by decide) (choices 1) [2,8,128] r26084 c26084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9265
  · exact u9266
  · exact u9267

def b26085 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 57, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 259 196 56 81 40 194 130 386), lower := (rows 37 259 196 56 81 40 64 128 256), losses := [] }

theorem u26085 : Upper (D 7) (R 7) [36,257,192,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26085 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26086 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 56 81 160 74 138 266), lower := (rows 37 259 196 56 81 160 64 128 256), losses := [] }

theorem u26086 : Upper (D 7) (R 7) [36,257,192,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26087 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(3,1)], upper := (rows 37 259 196 56 82 33 202 138 394), lower := (rows 37 259 196 56 82 33 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 24 16 39 64 128 256), good := (rows 37 289 229 56 120 33 64 128 256) }] }

theorem u26087 : Upper (D 7) (R 7) [36,257,192,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26088 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 40, targets := 193 },{ cop := 3, region := 197, targets := 2 }], pairs := [(0,1),(3,0),(3,6),(3,7)], upper := (rows 37 259 196 56 82 34 201 137 393), lower := (rows 37 259 196 56 82 34 64 128 256), losses := [] }

theorem u26088 : Upper (D 7) (R 7) [36,257,192,48,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26089 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 259 196 56 82 40 195 131 387), lower := (rows 37 259 196 56 82 40 64 128 256), losses := [] }

theorem u26089 : Upper (D 7) (R 7) [36,257,192,48,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26089 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26090 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 346, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 259 196 56 82 160 75 139 267), lower := (rows 37 259 196 56 82 160 64 128 256), losses := [] }

theorem u26090 : Upper (D 7) (R 7) [36,257,192,48,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26091 : Route 9 := (fun mask => (mask,id))

def c26091 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26091 : Upper (D 7) (R 7) [36,257,192,65,130,2] 13 := by
  apply FastRouting.sound _ _ [36,257,192,65,130,2] 13 (by decide) (choices 1) [8,16,32] r26091 c26091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9268
  · exact u9269
  · exact u9270

def b26092 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 41, targets := 130 }], pairs := [(0,1),(0,7),(3,1)], upper := (rows 37 259 196 73 146 40 114 178 306), lower := (rows 37 259 196 73 146 40 64 128 256), losses := [] }

theorem u26092 : Upper (D 7) (R 7) [36,257,192,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26092 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26093 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(1,7),(3,7)], upper := (rows 37 259 196 73 146 48 106 170 298), lower := (rows 37 259 196 73 146 48 64 128 256), losses := [] }

theorem u26093 : Upper (D 7) (R 7) [36,257,192,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26093 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26094 : Route 9 := (fun mask => (mask,id))

def c26094 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26094 : Upper (D 7) (R 7) [36,257,192,65,136,2] 13 := by
  apply FastRouting.sound _ _ [36,257,192,65,136,2] 13 (by decide) (choices 1) [2,16,32] r26094 c26094
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9271
  · exact u9272
  · exact u9273

def b26095 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 259 196 73 152 48 98 162 290), lower := (rows 37 259 196 73 152 48 64 128 256), losses := [] }

theorem u26095 : Upper (D 7) (R 7) [36,257,192,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26095 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r26096 : Route 9 := (fun mask => (mask,id))

def c26096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26096 : Upper (D 7) (R 7) [36,257,192,65,160,2] 13 := by
  apply FastRouting.sound _ _ [36,257,192,65,160,2] 13 (by decide) (choices 1) [2,8,16] r26096 c26096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9274
  · exact u9275
  · exact u9276

def b26097 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 57, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 37 259 196 73 176 40 82 146 274), lower := (rows 37 259 196 73 176 40 64 128 256), losses := [] }

theorem u26097 : Upper (D 7) (R 7) [36,257,192,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26097 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26098 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 259 196 73 176 48 74 138 266), lower := (rows 37 259 196 73 176 48 64 128 256), losses := [] }

theorem u26098 : Upper (D 7) (R 7) [36,257,192,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26098 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26099 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 259 196 74 146 33 120 184 312), lower := (rows 37 259 196 74 146 33 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 24 39 0 136 264), good := (rows 37 291 165 442 178 33 0 128 256) }] }

theorem u26099 : Upper (D 7) (R 7) [36,257,192,66,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u26099
end Delivery.IrregularNine14.P07
