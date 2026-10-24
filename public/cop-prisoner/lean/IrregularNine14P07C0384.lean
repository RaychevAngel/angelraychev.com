import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0119
import IrregularNine14P07C0120

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23040 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 37 74 84 137 50 33 450 386 386), lower := (rows 37 74 84 137 50 33 64 128 256), losses := [] }

theorem u23040 : Upper (D 7) (R 7) [36,72,80,129,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23041 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 453, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 74 84 137 50 34 449 385 385), lower := (rows 37 74 84 137 50 34 64 128 256), losses := [] }

theorem u23041 : Upper (D 7) (R 7) [36,72,80,129,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23042 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 4, region := 325, targets := 128 }], pairs := [(0,7),(1,5),(2,7),(3,5)], upper := (rows 37 74 84 137 50 160 323 387 259), lower := (rows 37 74 84 137 50 160 64 128 256), losses := [] }

theorem u23042 : Upper (D 7) (R 7) [36,72,80,129,34,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23043 : Route 9 := (fun mask => (mask,id))

def c23043 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23043 : Upper (D 7) (R 7) [36,72,80,129,34,256] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,34,256] 13 (by decide) (choices 1) [1,2,128] r23043 c23043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7197
  · exact u7198
  · exact u7199

def b23044 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 354, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 74 84 137 146 33 354 418 290), lower := (rows 37 74 84 137 146 33 64 128 256), losses := [] }

theorem u23044 : Upper (D 7) (R 7) [36,72,80,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23045 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 357, targets := 128 },{ cop := 0, region := 392, targets := 2 },{ cop := 0, region := 392, targets := 64 }], pairs := [(0,7),(2,7),(3,1),(3,6)], upper := (rows 37 74 84 137 146 34 353 417 289), lower := (rows 37 74 84 137 146 34 64 128 256), losses := [] }

theorem u23045 : Upper (D 7) (R 7) [36,72,80,129,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23046 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 357, targets := 128 },{ cop := 3, region := 354, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 84 137 146 288 99 163 291), lower := (rows 37 74 84 137 146 288 64 128 256), losses := [] }

theorem u23046 : Upper (D 7) (R 7) [36,72,80,129,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23046 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23047 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 84 137 176 33 322 386 258), lower := (rows 37 74 84 137 176 33 64 128 256), losses := [] }

theorem u23047 : Upper (D 7) (R 7) [36,72,80,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23048 : Route 9 := (fun mask => (mask,id))

def c23048 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23048 : Upper (D 7) (R 7) [36,72,80,129,160,2] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,160,2] 13 (by decide) (choices 1) [1,2,256] r23048 c23048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7200
  · exact u7201
  · exact u7202

def b23049 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 37 74 84 137 176 288 67 131 259), lower := (rows 37 74 84 137 176 288 64 128 256), losses := [] }

theorem u23049 : Upper (D 7) (R 7) [36,72,80,129,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23049 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23050 : Route 9 := (fun mask => (mask,id))

def c23050 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u23050 : Upper (D 7) (R 7) [36,72,80,129,257,2] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,257,2] 13 (by decide) (choices 1) [2,32,128] r23050 c23050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7203
  · exact u7204
  · exact u7205

def r23051 : Route 9 := (fun mask => (mask,id))

def c23051 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23051 : Upper (D 7) (R 7) [36,72,80,129,257,128] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,257,128] 13 (by decide) (choices 1) [2,32] r23051 c23051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7206
  · exact u7207

def b23052 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 74 84 137 274 33 226 162 418), lower := (rows 37 74 84 137 274 33 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 18 45 0 130 258), good := (rows 37 442 53 169 402 33 0 128 256) }] }

theorem u23052 : Upper (D 7) (R 7) [36,72,80,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23053 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 136, targets := 2 },{ cop := 0, region := 136, targets := 64 }], pairs := [(0,6),(0,7),(3,1),(3,6)], upper := (rows 37 74 84 137 274 34 225 161 417), lower := (rows 37 74 84 137 274 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 13 16 50 0 133 261), good := (rows 429 42 445 393 306 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 50 64 0 256), good := (rows 37 106 117 9 306 34 64 0 256) }] }

theorem u23053 : Upper (D 7) (R 7) [36,72,80,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23053 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23054 : Route 9 := (fun mask => (mask,id))

def c23054 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23054 : Upper (D 7) (R 7) [36,72,80,129,258,128] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,258,128] 13 (by decide) (choices 1) [1,2,32] r23054 c23054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7208
  · exact u7209
  · exact u7210

def b23055 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 202, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 84 137 304 33 194 130 386), lower := (rows 37 74 84 137 304 33 64 128 256), losses := [] }

theorem u23055 : Upper (D 7) (R 7) [36,72,80,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23056 : Route 9 := (fun mask => (mask,id))

def c23056 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23056 : Upper (D 7) (R 7) [36,72,80,129,288,2] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,288,2] 13 (by decide) (choices 1) [1,2,128] r23056 c23056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7211
  · exact u7212
  · exact u7213

def r23057 : Route 9 := (fun mask => (mask,id))

def c23057 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23057 : Upper (D 7) (R 7) [36,72,80,129,288,128] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,288,128] 13 (by decide) (choices 1) [1,2] r23057 c23057
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7214
  · exact u7215

def b23058 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 98, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 74 84 137 400 33 98 162 290), lower := (rows 37 74 84 137 400 33 64 128 256), losses := [] }

theorem u23058 : Upper (D 7) (R 7) [36,72,80,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23059 : Route 9 := (fun mask => (mask,id))

def c23059 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23059 : Upper (D 7) (R 7) [36,72,80,129,384,2] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,384,2] 13 (by decide) (choices 1) [1,2,32] r23059 c23059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7216
  · exact u7217
  · exact u7218

def b23060 : PairBound 9 := { available := 290, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 84 138 145 33 354 418 290), lower := (rows 37 74 84 138 145 33 64 128 256), losses := [] }

theorem u23060 : Upper (D 7) (R 7) [36,72,80,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23061 : PairBound 9 := { available := 289, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,1),(2,1),(4,1),(4,6)], upper := (rows 37 74 84 138 145 34 353 417 289), lower := (rows 37 74 84 138 145 34 64 128 256), losses := [] }

theorem u23061 : Upper (D 7) (R 7) [36,72,80,130,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23062 : Route 9 := (fun mask => (mask,id))

def c23062 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23062 : Upper (D 7) (R 7) [36,72,80,130,129,256] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130,129,256] 13 (by decide) (choices 1) [1,2,32] r23062 c23062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7219
  · exact u7220
  · exact u7221

def b23063 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 84 138 176 33 323 387 259), lower := (rows 37 74 84 138 176 33 64 128 256), losses := [] }

theorem u23063 : Upper (D 7) (R 7) [36,72,80,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23064 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 37 74 84 138 176 34 321 385 257), lower := (rows 37 74 84 138 176 34 64 128 256), losses := [] }

theorem u23064 : Upper (D 7) (R 7) [36,72,80,130,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23065 : Route 9 := (fun mask => (mask,id))

def c23065 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23065 : Upper (D 7) (R 7) [36,72,80,130,160,256] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130,160,256] 13 (by decide) (choices 1) [1,2] r23065 c23065
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7222
  · exact u7223

def b23066 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 202, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 84 138 273 33 226 162 418), lower := (rows 37 74 84 138 273 33 64 128 256), losses := [] }

theorem u23066 : Upper (D 7) (R 7) [36,72,80,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23067 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,1),(2,1),(4,1),(4,6)], upper := (rows 37 74 84 138 273 34 225 161 417), lower := (rows 37 74 84 138 273 34 64 128 256), losses := [] }

theorem u23067 : Upper (D 7) (R 7) [36,72,80,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23068 : Route 9 := (fun mask => (mask,id))

def c23068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23068 : Upper (D 7) (R 7) [36,72,80,130,257,128] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130,257,128] 13 (by decide) (choices 1) [1,2,32] r23068 c23068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7224
  · exact u7225
  · exact u7226

def b23069 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 2, region := 33, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 74 84 138 274 33 225 161 417), lower := (rows 37 74 84 138 274 33 64 128 256), losses := [] }

theorem u23069 : Upper (D 7) (R 7) [36,72,80,130,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23070 : Route 9 := (fun mask => (mask,id))

def c23070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23070 : Upper (D 7) (R 7) [36,72,80,130,258,128] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130,258,128] 13 (by decide) (choices 1) [1,32] r23070 c23070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7227
  · exact u7228

def b23071 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 202, targets := 32 }], pairs := [(0,1),(0,6),(0,7),(1,5)], upper := (rows 37 74 84 138 304 33 195 131 387), lower := (rows 37 74 84 138 304 33 64 128 256), losses := [] }

theorem u23071 : Upper (D 7) (R 7) [36,72,80,130,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23072 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 0, region := 202, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(4,1)], upper := (rows 37 74 84 138 304 34 193 129 385), lower := (rows 37 74 84 138 304 34 64 128 256), losses := [] }

theorem u23072 : Upper (D 7) (R 7) [36,72,80,130,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23073 : Route 9 := (fun mask => (mask,id))

def c23073 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23073 : Upper (D 7) (R 7) [36,72,80,130,288,128] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130,288,128] 13 (by decide) (choices 1) [1,2] r23073 c23073
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7229
  · exact u7230

def r23074 : Route 9 := (fun mask => (mask,id))

def c23074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23074 : Upper (D 7) (R 7) [36,72,80,130,384,1] 13 := by
  apply FastRouting.sound _ _ [36,72,80,130,384,1] 13 (by decide) (choices 1) [1,2,32] r23074 c23074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7231
  · exact u7232
  · exact u7233

def b23075 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 469, targets := 2 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,1),(2,1),(4,1),(4,6)], upper := (rows 37 74 84 138 400 34 97 161 289), lower := (rows 37 74 84 138 400 34 64 128 256), losses := [] }

theorem u23075 : Upper (D 7) (R 7) [36,72,80,130,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23076 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 84 168 19 33 450 386 386), lower := (rows 37 74 84 168 19 33 64 128 256), losses := [] }

theorem u23076 : Upper (D 7) (R 7) [36,72,80,160,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23077 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 452, targets := 2 }], pairs := [(0,7),(2,1),(2,7),(4,7)], upper := (rows 37 74 84 168 19 34 449 385 385), lower := (rows 37 74 84 168 19 34 64 128 256), losses := [] }

theorem u23077 : Upper (D 7) (R 7) [36,72,80,160,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23078 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 84 168 19 160 323 387 259), lower := (rows 37 74 84 168 19 160 64 128 256), losses := [] }

theorem u23078 : Upper (D 7) (R 7) [36,72,80,160,3,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23079 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 196, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,6),(2,5),(3,6)], upper := (rows 37 74 84 168 19 288 195 131 387), lower := (rows 37 74 84 168 19 288 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 28 16 308 0 144 272), good := (rows 45 10 445 168 443 288 0 128 288) }] }

theorem u23079 : Upper (D 7) (R 7) [36,72,80,160,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23079 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23080 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 458, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 84 168 145 33 322 386 258), lower := (rows 37 74 84 168 145 33 64 128 256), losses := [] }

theorem u23080 : Upper (D 7) (R 7) [36,72,80,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23081 : PairBound 9 := { available := 259, camps := [], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 84 168 145 34 323 387 259), lower := (rows 37 74 84 168 145 34 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 39 64 128 256), good := (rows 38 106 126 168 184 34 64 128 256) },{ target := 1, region := (rows 33 0 6 8 24 32 64 128 256), good := (rows 37 92 84 185 145 37 64 128 256) }] }

theorem u23081 : Upper (D 7) (R 7) [36,72,80,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23082 : Route 9 := (fun mask => (mask,id))

def c23082 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23082 : Upper (D 7) (R 7) [36,72,80,160,129,256] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,129,256] 13 (by decide) (choices 1) [1,2] r23082 c23082
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7234
  · exact u7235

def b23083 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(2,7)], upper := (rows 37 74 84 168 146 33 323 387 259), lower := (rows 37 74 84 168 146 33 64 128 256), losses := [] }

theorem u23083 : Upper (D 7) (R 7) [36,72,80,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23084 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 40, targets := 65 },{ cop := 4, region := 357, targets := 128 }], pairs := [(0,7),(2,7),(3,0),(3,6)], upper := (rows 37 74 84 168 146 34 321 385 257), lower := (rows 37 74 84 168 146 34 64 128 256), losses := [] }

theorem u23084 : Upper (D 7) (R 7) [36,72,80,160,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23085 : Route 9 := (fun mask => (mask,id))

def c23085 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23085 : Upper (D 7) (R 7) [36,72,80,160,130,256] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,130,256] 13 (by decide) (choices 1) [1,2] r23085 c23085
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7236
  · exact u7237

def b23086 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 0, region := 202, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 84 168 273 33 194 130 386), lower := (rows 37 74 84 168 273 33 64 128 256), losses := [] }

theorem u23086 : Upper (D 7) (R 7) [36,72,80,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23087 : Route 9 := (fun mask => (mask,id))

def c23087 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23087 : Upper (D 7) (R 7) [36,72,80,160,257,2] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,257,2] 13 (by decide) (choices 1) [1,2,128] r23087 c23087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7238
  · exact u7239
  · exact u7240

def b23088 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 84 168 273 160 67 131 259), lower := (rows 37 74 84 168 273 160 64 128 256), losses := [] }

theorem u23088 : Upper (D 7) (R 7) [36,72,80,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23089 : Route 9 := (fun mask => (mask,id))

def c23089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23089 : Upper (D 7) (R 7) [36,72,80,160,258,1] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,258,1] 13 (by decide) (choices 1) [1,2,128] r23089 c23089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7241
  · exact u7242
  · exact u7243

def b23090 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 136, targets := 2 },{ cop := 0, region := 136, targets := 64 }], pairs := [(0,6),(0,7),(3,1),(3,6)], upper := (rows 37 74 84 168 274 34 193 129 385), lower := (rows 37 74 84 168 274 34 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 13 16 50 0 133 261), good := (rows 429 42 445 168 306 34 0 128 256) },{ target := 7, region := (rows 5 2 4 8 16 50 64 0 256), good := (rows 37 106 117 40 306 34 64 0 256) }] }

theorem u23090 : Upper (D 7) (R 7) [36,72,80,160,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23091 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 84 168 274 160 67 131 259), lower := (rows 37 74 84 168 274 160 64 128 256), losses := [] }

theorem u23091 : Upper (D 7) (R 7) [36,72,80,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23092 : Route 9 := (fun mask => (mask,id))

def c23092 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23092 : Upper (D 7) (R 7) [36,72,80,160,384,1] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,384,1] 13 (by decide) (choices 1) [1,2] r23092 c23092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7244
  · exact u7245

def r23093 : Route 9 := (fun mask => (mask,id))

def c23093 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23093 : Upper (D 7) (R 7) [36,72,80,160,384,2] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,384,2] 13 (by decide) (choices 1) [1,2] r23093 c23093
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7246
  · exact u7247

def b23094 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 37 74 84 265 50 33 194 130 386), lower := (rows 37 74 84 265 50 33 64 128 256), losses := [] }

theorem u23094 : Upper (D 7) (R 7) [36,72,80,257,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23095 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 53, targets := 128 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 74 84 265 50 34 193 129 385), lower := (rows 37 74 84 265 50 34 64 128 256), losses := [] }

theorem u23095 : Upper (D 7) (R 7) [36,72,80,257,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23096 : Route 9 := (fun mask => (mask,id))

def c23096 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u23096 : Upper (D 7) (R 7) [36,72,80,257,34,128] 13 := by
  apply FastRouting.sound _ _ [36,72,80,257,34,128] 13 (by decide) (choices 1) [1,2,128] r23096 c23096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7248
  · exact u7249
  · exact u7250

def r23097 : Route 9 := (fun mask => (mask,id))

def c23097 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u23097 : Upper (D 7) (R 7) [36,72,80,257,129,2] 13 := by
  apply FastRouting.sound _ _ [36,72,80,257,129,2] 13 (by decide) (choices 1) [2,32,128] r23097 c23097
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7251
  · exact u7252
  · exact u7253

def b23098 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 330, targets := 128 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(3,7)], upper := (rows 37 74 84 265 145 160 98 162 290), lower := (rows 37 74 84 265 145 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 176 64 128 256), good := (rows 37 72 117 265 177 160 64 160 256) }] }

theorem u23098 : Upper (D 7) (R 7) [36,72,80,257,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23099 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(4,6)], upper := (rows 37 74 84 265 146 33 226 162 418), lower := (rows 37 74 84 265 146 33 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 18 45 0 130 258), good := (rows 37 442 53 297 402 33 0 128 256) }] }

theorem u23099 : Upper (D 7) (R 7) [36,72,80,257,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u23099
end Delivery.IrregularNine14.P07
