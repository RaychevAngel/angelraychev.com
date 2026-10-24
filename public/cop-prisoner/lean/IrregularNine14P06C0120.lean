import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0009

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7200 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 35 134 262 73 84 40 80 161 289), lower := (rows 35 134 262 73 84 40 80 128 256), losses := [] }

theorem u7200 : Upper (D 6) (R 6) [34,132,258,65,68,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7200 [(5,3),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7201 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 262 73 84 40 96 145 273), lower := (rows 35 134 262 73 84 40 96 128 256), losses := [] }

theorem u7201 : Upper (D 6) (R 6) [34,132,258,65,68,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7201 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7202 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 300, targets := 2 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 35 134 268 13 81 96 66 176 304), lower := (rows 35 134 268 13 81 96 66 128 256), losses := [] }

theorem u7202 : Upper (D 6) (R 6) [34,132,264,5,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7203 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 268 13 81 96 80 162 290), lower := (rows 35 134 268 13 81 96 80 128 256), losses := [] }

theorem u7203 : Upper (D 6) (R 6) [34,132,264,5,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7203 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7204 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 134 268 13 81 96 96 146 274), lower := (rows 35 134 268 13 81 96 96 128 256), losses := [] }

theorem u7204 : Upper (D 6) (R 6) [34,132,264,5,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7205 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 268 13 82 96 65 176 304), lower := (rows 35 134 268 13 82 96 65 128 256), losses := [] }

theorem u7205 : Upper (D 6) (R 6) [34,132,264,5,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7206 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 268 13 82 96 80 161 289), lower := (rows 35 134 268 13 82 96 80 128 256), losses := [] }

theorem u7206 : Upper (D 6) (R 6) [34,132,264,5,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7206 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7207 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 80, targets := 1 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 35 134 268 13 82 96 96 145 273), lower := (rows 35 134 268 13 82 96 96 128 256), losses := [] }

theorem u7207 : Upper (D 6) (R 6) [34,132,264,5,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7208 : Route 9 := (fun mask => (mask,id))

def c7208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7208 : Upper (D 6) (R 6) [34,132,264,18,5,64,1] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,5,64,1] 13 (by decide) (choices 1) [32,64] r7208 c7208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u549
  · exact u550

def r7209 : Route 9 := (fun mask => (mask,id))

def c7209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7209 : Upper (D 6) (R 6) [34,132,264,18,5,64,32] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,5,64,32] 13 (by decide) (choices 1) [1,64] r7209 c7209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u551
  · exact u552

def r7210 : Route 9 := (fun mask => (mask,id))

def c7210 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7210 : Upper (D 6) (R 6) [34,132,264,18,36,64,1] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,36,64,1] 13 (by decide) (choices 1) [1,64] r7210 c7210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u553
  · exact u554

def b7211 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 134 268 26 81 96 65 164 292), lower := (rows 35 134 268 26 81 96 65 128 256), losses := [] }

theorem u7211 : Upper (D 6) (R 6) [34,132,264,18,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7212 : PairBound 9 := { available := 33, camps := [], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 134 268 26 81 96 68 161 289), lower := (rows 35 134 268 26 81 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 127 78 145 273), good := (rows 497 228 364 508 497 96 100 128 256) },{ target := 2, region := (rows 9 2 0 8 16 112 64 153 281), good := (rows 419 130 393 443 497 96 96 128 256) }] }

theorem u7212 : Upper (D 6) (R 6) [34,132,264,18,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7213 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 134 268 26 81 96 96 133 261), lower := (rows 35 134 268 26 81 96 96 128 256), losses := [] }

theorem u7213 : Upper (D 6) (R 6) [34,132,264,18,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7214 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 268 26 84 33 65 224 352), lower := (rows 35 134 268 26 84 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 97 97 241 369), good := (rows 481 132 268 412 500 481 481 128 256) }] }

theorem u7214 : Upper (D 6) (R 6) [34,132,264,18,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7215 : Route 9 := (fun mask => (mask,id))

def c7215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7215 : Upper (D 6) (R 6) [34,132,264,18,68,1,32] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,68,1,32] 13 (by decide) (choices 1) [1,64] r7215 c7215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u555
  · exact u556

def r7216 : Route 9 := (fun mask => (mask,id))

def c7216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7216 : Upper (D 6) (R 6) [34,132,264,18,68,64,1] 13 := by
  apply FastRouting.sound _ _ [34,132,264,18,68,64,1] 13 (by decide) (choices 1) [1,32] r7216 c7216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u557
  · exact u558

def b7217 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 120, targets := 1 },{ cop := 1, region := 112, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 35 134 268 26 84 96 96 129 257), lower := (rows 35 134 268 26 84 96 96 128 256), losses := [] }

theorem u7217 : Upper (D 6) (R 6) [34,132,264,18,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7218 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 398, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 134 268 26 112 33 65 196 324), lower := (rows 35 134 268 26 112 33 65 128 256), losses := [] }

theorem u7218 : Upper (D 6) (R 6) [34,132,264,18,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7219 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,0)], upper := (rows 35 134 268 26 112 33 68 193 321), lower := (rows 35 134 268 26 112 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 17 32 70 128 256), good := (rows 122 198 332 90 112 56 68 128 256) }] }

theorem u7219 : Upper (D 6) (R 6) [34,132,264,18,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7220 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 268 28 82 96 65 161 289), lower := (rows 35 134 268 28 82 96 65 128 256), losses := [] }

theorem u7220 : Upper (D 6) (R 6) [34,132,264,20,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7221 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 120, targets := 1 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(3,0),(4,0)], upper := (rows 35 134 268 28 82 96 96 129 257), lower := (rows 35 134 268 28 82 96 96 128 256), losses := [] }

theorem u7221 : Upper (D 6) (R 6) [34,132,264,20,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7222 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 130, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 134 268 56 84 33 65 194 322), lower := (rows 35 134 268 56 84 33 65 128 256), losses := [] }

theorem u7222 : Upper (D 6) (R 6) [34,132,264,48,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7223 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 35 134 268 56 84 33 66 193 321), lower := (rows 35 134 268 56 84 33 66 128 256), losses := [] }

theorem u7223 : Upper (D 6) (R 6) [34,132,264,48,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7224 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 3, region := 308, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 35 134 268 73 21 96 66 176 304), lower := (rows 35 134 268 73 21 96 66 128 256), losses := [] }

theorem u7224 : Upper (D 6) (R 6) [34,132,264,65,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7225 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 134 268 73 21 96 80 162 290), lower := (rows 35 134 268 73 21 96 80 128 256), losses := [] }

theorem u7225 : Upper (D 6) (R 6) [34,132,264,65,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7225 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7226 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 134 268 73 21 96 96 146 274), lower := (rows 35 134 268 73 21 96 96 128 256), losses := [] }

theorem u7226 : Upper (D 6) (R 6) [34,132,264,65,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7227 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 0, region := 72, targets := 32 }], pairs := [(0,2),(3,2),(3,5)], upper := (rows 35 134 268 74 21 96 65 176 304), lower := (rows 35 134 268 74 21 96 65 128 256), losses := [] }

theorem u7227 : Upper (D 6) (R 6) [34,132,264,66,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7228 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(1,6)], upper := (rows 35 134 268 74 21 96 80 161 289), lower := (rows 35 134 268 74 21 96 80 128 256), losses := [{ target := 6, region := (rows 1 18 4 8 16 32 0 129 257), good := (rows 419 134 268 10 407 32 18 128 256) }] }

theorem u7228 : Upper (D 6) (R 6) [34,132,264,66,5,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7228 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7229 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 4, region := 130, targets := 32 }], pairs := [(0,2),(1,5),(3,2)], upper := (rows 35 134 268 74 21 96 96 145 273), lower := (rows 35 134 268 74 21 96 96 128 256), losses := [] }

theorem u7229 : Upper (D 6) (R 6) [34,132,264,66,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7230 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 3, region := 210, targets := 32 }], pairs := [(0,2),(1,5),(4,2)], upper := (rows 35 134 292 13 81 96 66 152 280), lower := (rows 35 134 292 13 81 96 66 128 256), losses := [] }

theorem u7230 : Upper (D 6) (R 6) [34,132,288,5,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7231 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 134 292 13 81 96 72 146 274), lower := (rows 35 134 292 13 81 96 72 128 256), losses := [] }

theorem u7231 : Upper (D 6) (R 6) [34,132,288,5,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7231 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7232 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 292 13 81 96 80 138 266), lower := (rows 35 134 292 13 81 96 80 128 256), losses := [] }

theorem u7232 : Upper (D 6) (R 6) [34,132,288,5,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7232 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7233 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 80, targets := 6 },{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,1),(4,2)], upper := (rows 35 134 292 13 88 96 65 146 274), lower := (rows 35 134 292 13 88 96 65 128 256), losses := [] }

theorem u7233 : Upper (D 6) (R 6) [34,132,288,5,72,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7234 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 134 292 13 88 96 66 145 273), lower := (rows 35 134 292 13 88 96 66 128 256), losses := [] }

theorem u7234 : Upper (D 6) (R 6) [34,132,288,5,72,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7235 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 292 13 88 96 80 131 259), lower := (rows 35 134 292 13 88 96 80 128 256), losses := [] }

theorem u7235 : Upper (D 6) (R 6) [34,132,288,5,72,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7235 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7236 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 390, targets := 1 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 134 292 25 28 96 65 194 322), lower := (rows 35 134 292 25 28 96 65 128 256), losses := [] }

theorem u7236 : Upper (D 6) (R 6) [34,132,288,17,12,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7237 : Route 9 := (fun mask => (mask,id))

def c7237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7237 : Upper (D 6) (R 6) [34,132,288,17,12,64,2] 13 := by
  apply FastRouting.sound _ _ [34,132,288,17,12,64,2] 13 (by decide) (choices 1) [1,64] r7237 c7237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u559
  · exact u560

def b7238 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 35 134 292 25 84 33 66 200 328), lower := (rows 35 134 292 25 84 33 66 128 256), losses := [] }

theorem u7238 : Upper (D 6) (R 6) [34,132,288,17,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7239 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 292 25 84 33 72 194 322), lower := (rows 35 134 292 25 84 33 72 128 256), losses := [] }

theorem u7239 : Upper (D 6) (R 6) [34,132,288,17,68,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7239 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7240 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 292 25 84 40 65 194 322), lower := (rows 35 134 292 25 84 40 65 128 256), losses := [] }

theorem u7240 : Upper (D 6) (R 6) [34,132,288,17,68,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7240 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7241 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 80, targets := 33 }], pairs := [(4,0),(4,5)], upper := (rows 35 134 292 25 84 40 66 193 321), lower := (rows 35 134 292 25 84 40 66 128 256), losses := [] }

theorem u7241 : Upper (D 6) (R 6) [34,132,288,17,68,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7241 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7242 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 134 292 25 84 96 65 138 266), lower := (rows 35 134 292 25 84 96 65 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 112 64 136 264), good := (rows 34 134 292 446 116 96 96 128 256) }] }

theorem u7242 : Upper (D 6) (R 6) [34,132,288,17,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7243 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 97, targets := 4 },{ cop := 1, region := 80, targets := 32 }], pairs := [(0,2),(4,0),(4,5)], upper := (rows 35 134 292 25 84 96 66 137 265), lower := (rows 35 134 292 25 84 96 66 128 256), losses := [] }

theorem u7243 : Upper (D 6) (R 6) [34,132,288,17,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7244 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 292 25 84 96 72 131 259), lower := (rows 35 134 292 25 84 96 72 128 256), losses := [] }

theorem u7244 : Upper (D 6) (R 6) [34,132,288,17,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7244 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7245 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 134 292 26 81 96 65 140 268), lower := (rows 35 134 292 26 81 96 65 128 256), losses := [] }

theorem u7245 : Upper (D 6) (R 6) [34,132,288,18,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7246 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 134 292 26 81 96 68 137 265), lower := (rows 35 134 292 26 81 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 260 8 17 383 326 128 256), good := (rows 113 228 356 120 113 96 100 128 356) }] }

theorem u7246 : Upper (D 6) (R 6) [34,132,288,18,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7247 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 121, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 134 292 26 81 96 72 133 261), lower := (rows 35 134 292 26 81 96 72 128 256), losses := [] }

theorem u7247 : Upper (D 6) (R 6) [34,132,288,18,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7247 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7248 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 138, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 292 26 84 33 65 200 328), lower := (rows 35 134 292 26 84 33 65 128 256), losses := [] }

theorem u7248 : Upper (D 6) (R 6) [34,132,288,18,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7249 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 88, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 35 134 292 26 84 33 72 193 321), lower := (rows 35 134 292 26 84 33 72 128 256), losses := [] }

theorem u7249 : Upper (D 6) (R 6) [34,132,288,18,68,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7249 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7250 : Route 9 := (fun mask => (mask,id))

def c7250 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7250 : Upper (D 6) (R 6) [34,132,288,18,68,64,1] 13 := by
  apply FastRouting.sound _ _ [34,132,288,18,68,64,1] 13 (by decide) (choices 1) [1,8] r7250 c7250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u561
  · exact u562

def b7251 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 292 26 84 96 72 129 257), lower := (rows 35 134 292 26 84 96 72 128 256), losses := [] }

theorem u7251 : Upper (D 6) (R 6) [34,132,288,18,68,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7251 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7252 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 130, targets := 97 }], pairs := [(1,0),(1,5),(1,6)], upper := (rows 35 134 292 28 81 96 65 138 266), lower := (rows 35 134 292 28 81 96 65 128 256), losses := [] }

theorem u7252 : Upper (D 6) (R 6) [34,132,288,20,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7253 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 300, targets := 2 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 35 134 292 28 81 96 66 137 265), lower := (rows 35 134 292 28 81 96 66 128 256), losses := [] }

theorem u7253 : Upper (D 6) (R 6) [34,132,288,20,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7254 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 292 28 81 96 72 131 259), lower := (rows 35 134 292 28 81 96 72 128 256), losses := [] }

theorem u7254 : Upper (D 6) (R 6) [34,132,288,20,65,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7254 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7255 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 292 28 82 33 65 200 328), lower := (rows 35 134 292 28 82 33 65 128 256), losses := [] }

theorem u7255 : Upper (D 6) (R 6) [34,132,288,20,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7256 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 88, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 35 134 292 28 82 33 72 193 321), lower := (rows 35 134 292 28 82 33 72 128 256), losses := [] }

theorem u7256 : Upper (D 6) (R 6) [34,132,288,20,66,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7256 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7257 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(0,2),(4,2),(4,5)], upper := (rows 35 134 292 28 82 96 65 137 265), lower := (rows 35 134 292 28 82 96 65 128 256), losses := [] }

theorem u7257 : Upper (D 6) (R 6) [34,132,288,20,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7258 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 292 28 82 96 72 129 257), lower := (rows 35 134 292 28 82 96 72 128 256), losses := [] }

theorem u7258 : Upper (D 6) (R 6) [34,132,288,20,66,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7258 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7259 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 292 28 88 33 65 194 322), lower := (rows 35 134 292 28 88 33 65 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 32 64 144 272), good := (rows 34 134 292 414 474 32 64 128 256) }] }

theorem u7259 : Upper (D 6) (R 6) [34,132,288,20,72,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7259
end Delivery.IrregularNine14.P06
