import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0118
import IrregularNine14P06C0119

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23220 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 73 280 36 83 147 275), lower := (rows 35 134 100 73 280 36 64 128 256), losses := [] }

theorem u23220 : Upper (D 6) (R 6) [34,132,96,65,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23221 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 73 280 48 71 135 263), lower := (rows 35 134 100 73 280 48 64 128 256), losses := [] }

theorem u23221 : Upper (D 6) (R 6) [34,132,96,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23221 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23222 : Route 9 := (fun mask => (mask,id))

def c23222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23222 : Upper (D 6) (R 6) [34,132,96,66,257,1] 13 := by
  apply FastRouting.sound _ _ [34,132,96,66,257,1] 13 (by decide) (choices 1) [4,8,16] r23222 c23222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7114
  · exact u7115
  · exact u7116

def b23223 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 74 273 36 89 153 281), lower := (rows 35 134 100 74 273 36 64 128 256), losses := [] }

theorem u23223 : Upper (D 6) (R 6) [34,132,96,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23224 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 74 273 40 85 149 277), lower := (rows 35 134 100 74 273 40 64 128 256), losses := [] }

theorem u23224 : Upper (D 6) (R 6) [34,132,96,66,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23224 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23225 : Route 9 := (fun mask => (mask,id))

def c23225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23225 : Upper (D 6) (R 6) [34,132,96,66,257,16] 13 := by
  apply FastRouting.sound _ _ [34,132,96,66,257,16] 13 (by decide) (choices 1) [1,4,8] r23225 c23225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7117
  · exact u7118
  · exact u7119

def r23226 : Route 9 := (fun mask => (mask,id))

def c23226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23226 : Upper (D 6) (R 6) [34,132,96,66,260,1] 13 := by
  apply FastRouting.sound _ _ [34,132,96,66,260,1] 13 (by decide) (choices 1) [1,8,16] r23226 c23226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7120
  · exact u7121
  · exact u7122

def b23227 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 74 276 40 81 145 273), lower := (rows 35 134 100 74 276 40 64 128 256), losses := [] }

theorem u23227 : Upper (D 6) (R 6) [34,132,96,66,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23227 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23228 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 100 74 276 48 73 137 265), lower := (rows 35 134 100 74 276 48 64 128 256), losses := [] }

theorem u23228 : Upper (D 6) (R 6) [34,132,96,66,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23228 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23229 : Route 9 := (fun mask => (mask,id))

def c23229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23229 : Upper (D 6) (R 6) [34,132,96,66,264,1] 13 := by
  apply FastRouting.sound _ _ [34,132,96,66,264,1] 13 (by decide) (choices 1) [1,4,16] r23229 c23229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7123
  · exact u7124
  · exact u7125

def b23230 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 74 280 36 81 145 273), lower := (rows 35 134 100 74 280 36 64 128 256), losses := [] }

theorem u23230 : Upper (D 6) (R 6) [34,132,96,66,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23231 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 74 280 48 69 133 261), lower := (rows 35 134 100 74 280 48 64 128 256), losses := [] }

theorem u23231 : Upper (D 6) (R 6) [34,132,96,66,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23231 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23232 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 100 88 273 33 78 142 270), lower := (rows 35 134 100 88 273 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 64 128 256), good := (rows 33 132 100 124 305 33 64 128 256) }] }

theorem u23232 : Upper (D 6) (R 6) [34,132,96,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23233 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 88 273 34 77 141 269), lower := (rows 35 134 100 88 273 34 64 128 256), losses := [] }

theorem u23233 : Upper (D 6) (R 6) [34,132,96,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23234 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 88 273 36 75 139 267), lower := (rows 35 134 100 88 273 36 64 128 256), losses := [] }

theorem u23234 : Upper (D 6) (R 6) [34,132,96,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23235 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 88 273 40 71 135 263), lower := (rows 35 134 100 88 273 40 64 128 256), losses := [] }

theorem u23235 : Upper (D 6) (R 6) [34,132,96,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23235 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23236 : Route 9 := (fun mask => (mask,id))

def c23236 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23236 : Upper (D 6) (R 6) [34,132,96,80,258,1] 13 := by
  apply FastRouting.sound _ _ [34,132,96,80,258,1] 13 (by decide) (choices 1) [1,4,8] r23236 c23236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7126
  · exact u7127
  · exact u7128

def b23237 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 88 274 36 73 137 265), lower := (rows 35 134 100 88 274 36 64 128 256), losses := [] }

theorem u23237 : Upper (D 6) (R 6) [34,132,96,80,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23238 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 88 274 40 69 133 261), lower := (rows 35 134 100 88 274 40 64 128 256), losses := [] }

theorem u23238 : Upper (D 6) (R 6) [34,132,96,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23238 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23239 : Route 9 := (fun mask => (mask,id))

def c23239 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23239 : Upper (D 6) (R 6) [34,132,96,80,260,1] 13 := by
  apply FastRouting.sound _ _ [34,132,96,80,260,1] 13 (by decide) (choices 1) [1,2,8] r23239 c23239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7129
  · exact u7130
  · exact u7131

def b23240 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 88 276 34 73 137 265), lower := (rows 35 134 100 88 276 34 64 128 256), losses := [] }

theorem u23240 : Upper (D 6) (R 6) [34,132,96,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23241 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 100 88 276 40 67 131 259), lower := (rows 35 134 100 88 276 40 64 128 256), losses := [] }

theorem u23241 : Upper (D 6) (R 6) [34,132,96,80,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23241 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23242 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 131, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 100 88 280 33 71 135 263), lower := (rows 35 134 100 88 280 33 64 128 256), losses := [] }

theorem u23242 : Upper (D 6) (R 6) [34,132,96,80,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23243 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 100 88 280 34 69 133 261), lower := (rows 35 134 100 88 280 34 64 128 256), losses := [] }

theorem u23243 : Upper (D 6) (R 6) [34,132,96,80,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23244 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 100 88 280 36 67 131 259), lower := (rows 35 134 100 88 280 36 64 128 256), losses := [] }

theorem u23244 : Upper (D 6) (R 6) [34,132,96,80,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23245 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 25 52 34 72 200 328), lower := (rows 35 134 261 25 52 34 64 128 256), losses := [] }

theorem u23245 : Upper (D 6) (R 6) [34,132,257,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23246 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 56, targets := 66 }], pairs := [(3,1),(3,6)], upper := (rows 35 134 261 25 52 40 66 194 322), lower := (rows 35 134 261 25 52 40 64 128 256), losses := [] }

theorem u23246 : Upper (D 6) (R 6) [34,132,257,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23246 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23247 : Route 9 := (fun mask => (mask,id))

def c23247 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23247 : Upper (D 6) (R 6) [34,132,257,17,36,64] 13 := by
  apply FastRouting.sound _ _ [34,132,257,17,36,64] 13 (by decide) (choices 1) [2,8] r23247 c23247
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7132
  · exact u7133

def b23248 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 261 25 82 36 104 232 360), lower := (rows 35 134 261 25 82 36 64 128 256), losses := [] }

theorem u23248 : Upper (D 6) (R 6) [34,132,257,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23249 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 134 261 25 82 40 100 228 356), lower := (rows 35 134 261 25 82 40 64 128 256), losses := [] }

theorem u23249 : Upper (D 6) (R 6) [34,132,257,17,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23249 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23250 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 3, region := 356, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 35 134 261 25 82 96 108 172 300), lower := (rows 35 134 261 25 82 96 64 128 256), losses := [] }

theorem u23250 : Upper (D 6) (R 6) [34,132,257,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23251 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 25 84 34 104 232 360), lower := (rows 35 134 261 25 84 34 64 128 256), losses := [] }

theorem u23251 : Upper (D 6) (R 6) [34,132,257,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23252 : PairBound 9 := { available := 98, camps := [], pairs := [(1,0),(4,0)], upper := (rows 35 134 261 25 84 40 98 226 354), lower := (rows 35 134 261 25 84 40 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 20 40 65 129 257), good := (rows 482 150 470 504 86 40 64 128 256) }] }

theorem u23252 : Upper (D 6) (R 6) [34,132,257,17,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23252 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23253 : Route 9 := (fun mask => (mask,id))

def c23253 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23253 : Upper (D 6) (R 6) [34,132,257,17,68,64] 13 := by
  apply FastRouting.sound _ _ [34,132,257,17,68,64] 13 (by decide) (choices 1) [2,8,32] r23253 c23253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7134
  · exact u7135
  · exact u7136

def b23254 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 25 88 34 100 228 356), lower := (rows 35 134 261 25 88 34 64 128 256), losses := [] }

theorem u23254 : Upper (D 6) (R 6) [34,132,257,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23255 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 261 25 88 36 98 226 354), lower := (rows 35 134 261 25 88 36 64 128 256), losses := [] }

theorem u23255 : Upper (D 6) (R 6) [34,132,257,17,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23256 : PairBound 9 := { available := 38, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 261 25 88 96 102 166 294), lower := (rows 35 134 261 25 88 96 64 128 256), losses := [] }

theorem u23256 : Upper (D 6) (R 6) [34,132,257,17,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23257 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 25 112 34 76 204 332), lower := (rows 35 134 261 25 112 34 64 128 256), losses := [] }

theorem u23257 : Upper (D 6) (R 6) [34,132,257,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23258 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(3,2),(4,2)], upper := (rows 35 134 261 25 112 36 74 202 330), lower := (rows 35 134 261 25 112 36 64 128 256), losses := [] }

theorem u23258 : Upper (D 6) (R 6) [34,132,257,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23259 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 261 25 112 40 70 198 326), lower := (rows 35 134 261 25 112 40 64 128 256), losses := [] }

theorem u23259 : Upper (D 6) (R 6) [34,132,257,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23259 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23260 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 261 25 112 96 78 142 270), lower := (rows 35 134 261 25 112 96 64 128 256), losses := [] }

theorem u23260 : Upper (D 6) (R 6) [34,132,257,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23261 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 261 26 52 33 72 200 328), lower := (rows 35 134 261 26 52 33 64 128 256), losses := [] }

theorem u23261 : Upper (D 6) (R 6) [34,132,257,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23262 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 134 261 26 52 40 65 193 321), lower := (rows 35 134 261 26 52 40 64 128 256), losses := [] }

theorem u23262 : Upper (D 6) (R 6) [34,132,257,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23262 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23263 : Route 9 := (fun mask => (mask,id))

def c23263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23263 : Upper (D 6) (R 6) [34,132,257,18,36,64] 13 := by
  apply FastRouting.sound _ _ [34,132,257,18,36,64] 13 (by decide) (choices 1) [1,8] r23263 c23263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7137
  · exact u7138

def b23264 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 261 26 81 36 104 232 360), lower := (rows 35 134 261 26 81 36 64 128 256), losses := [] }

theorem u23264 : Upper (D 6) (R 6) [34,132,257,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23265 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 261 26 81 40 100 228 356), lower := (rows 35 134 261 26 81 40 64 128 256), losses := [] }

theorem u23265 : Upper (D 6) (R 6) [34,132,257,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23265 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23266 : Route 9 := (fun mask => (mask,id))

def c23266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23266 : Upper (D 6) (R 6) [34,132,257,18,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,257,18,65,64] 13 (by decide) (choices 1) [4,8,32] r23266 c23266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7139
  · exact u7140
  · exact u7141

def b23267 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 261 26 84 33 104 232 360), lower := (rows 35 134 261 26 84 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 30 20 32 65 129 257), good := (rows 490 158 478 26 94 480 64 128 256) }] }

theorem u23267 : Upper (D 6) (R 6) [34,132,257,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23268 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 261 26 84 40 97 225 353), lower := (rows 35 134 261 26 84 40 64 128 256), losses := [] }

theorem u23268 : Upper (D 6) (R 6) [34,132,257,18,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23268 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23269 : Route 9 := (fun mask => (mask,id))

def c23269 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23269 : Upper (D 6) (R 6) [34,132,257,18,68,64] 13 := by
  apply FastRouting.sound _ _ [34,132,257,18,68,64] 13 (by decide) (choices 1) [1,8,32] r23269 c23269
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7142
  · exact u7143
  · exact u7144

def b23270 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 134 261 26 88 33 100 228 356), lower := (rows 35 134 261 26 88 33 64 128 256), losses := [] }

theorem u23270 : Upper (D 6) (R 6) [34,132,257,18,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23271 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(3,2),(4,2)], upper := (rows 35 134 261 26 88 36 97 225 353), lower := (rows 35 134 261 26 88 36 64 128 256), losses := [] }

theorem u23271 : Upper (D 6) (R 6) [34,132,257,18,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23272 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 261 26 88 96 101 165 293), lower := (rows 35 134 261 26 88 96 64 128 256), losses := [] }

theorem u23272 : Upper (D 6) (R 6) [34,132,257,18,72,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23273 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 261 26 112 33 76 204 332), lower := (rows 35 134 261 26 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 13 17 32 70 134 262), good := (rows 506 462 478 474 112 56 64 128 256) }] }

theorem u23273 : Upper (D 6) (R 6) [34,132,257,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23274 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 261 26 112 36 73 201 329), lower := (rows 35 134 261 26 112 36 64 128 256), losses := [] }

theorem u23274 : Upper (D 6) (R 6) [34,132,257,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23275 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 134 261 26 112 40 69 197 325), lower := (rows 35 134 261 26 112 40 64 128 256), losses := [] }

theorem u23275 : Upper (D 6) (R 6) [34,132,257,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23275 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23276 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 261 26 112 96 77 141 269), lower := (rows 35 134 261 26 112 96 64 128 256), losses := [] }

theorem u23276 : Upper (D 6) (R 6) [34,132,257,18,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23277 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 261 28 81 34 104 232 360), lower := (rows 35 134 261 28 81 34 64 128 256), losses := [] }

theorem u23277 : Upper (D 6) (R 6) [34,132,257,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23278 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 80, targets := 4 },{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(4,2)], upper := (rows 35 134 261 28 81 40 98 226 354), lower := (rows 35 134 261 28 81 40 64 128 256), losses := [] }

theorem u23278 : Upper (D 6) (R 6) [34,132,257,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23278 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23279 : Route 9 := (fun mask => (mask,id))

def c23279 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23279 : Upper (D 6) (R 6) [34,132,257,20,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,257,20,65,64] 13 (by decide) (choices 1) [2,8,32] r23279 c23279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7145
  · exact u7146
  · exact u7147

#print axioms u23279
end Delivery.IrregularNine14.P06
