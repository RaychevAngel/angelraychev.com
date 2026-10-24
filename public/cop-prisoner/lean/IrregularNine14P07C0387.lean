import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0122

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23220 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 133 296 146 33 82 210 338), lower := (rows 37 74 133 296 146 33 64 128 256), losses := [] }

theorem u23220 : Upper (D 7) (R 7) [36,72,129,288,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23220 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23221 : Route 9 := (fun mask => (mask,id))

def c23221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23221 : Upper (D 7) (R 7) [36,72,129,288,130,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,288,130,2] 13 (by decide) (choices 1) [1,16] r23221 c23221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7330
  · exact u7331

def b23222 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 133 296 146 48 67 195 323), lower := (rows 37 74 133 296 146 48 64 128 256), losses := [] }

theorem u23222 : Upper (D 7) (R 7) [36,72,129,288,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23222 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23223 : Route 9 := (fun mask => (mask,id))

def c23223 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23223 : Upper (D 7) (R 7) [36,72,129,288,130,64] 13 := by
  apply FastRouting.sound _ _ [36,72,129,288,130,64] 13 (by decide) (choices 1) [1,2,16] r23223 c23223
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7332
  · exact u7333
  · exact u7334

def b23224 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 37 74 133 296 208 33 82 146 274), lower := (rows 37 74 133 296 208 33 64 128 256), losses := [] }

theorem u23224 : Upper (D 7) (R 7) [36,72,129,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23225 : Route 9 := (fun mask => (mask,id))

def c23225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23225 : Upper (D 7) (R 7) [36,72,129,288,192,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,288,192,2] 13 (by decide) (choices 1) [1,2,16] r23225 c23225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7335
  · exact u7336
  · exact u7337

def b23226 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 74 133 296 208 48 67 131 259), lower := (rows 37 74 133 296 208 48 64 128 256), losses := [] }

theorem u23226 : Upper (D 7) (R 7) [36,72,129,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23226 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23227 : Route 9 := (fun mask => (mask,id))

def c23227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23227 : Upper (D 7) (R 7) [36,72,129,384,3,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384,3,2] 13 (by decide) (choices 1) [16,32] r23227 c23227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7338
  · exact u7339

def r23228 : Route 9 := (fun mask => (mask,id))

def c23228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23228 : Upper (D 7) (R 7) [36,72,129,384,3,16] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384,3,16] 13 (by decide) (choices 1) [2,32] r23228 c23228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7340
  · exact u7341

def r23229 : Route 9 := (fun mask => (mask,id))

def c23229 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23229 : Upper (D 7) (R 7) [36,72,129,384,3,64] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384,3,64] 13 (by decide) (choices 1) [2,16,32] r23229 c23229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7342
  · exact u7343
  · exact u7344

def b23230 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 392 50 33 82 210 338), lower := (rows 37 74 133 392 50 33 64 128 256), losses := [] }

theorem u23230 : Upper (D 7) (R 7) [36,72,129,384,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23231 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 48, targets := 193 },{ cop := 4, region := 197, targets := 2 }], pairs := [(0,1),(4,0),(4,6),(4,7)], upper := (rows 37 74 133 392 50 34 81 209 337), lower := (rows 37 74 133 392 50 34 64 128 256), losses := [] }

theorem u23231 : Upper (D 7) (R 7) [36,72,129,384,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23232 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 133 392 50 48 67 195 323), lower := (rows 37 74 133 392 50 48 64 128 256), losses := [] }

theorem u23232 : Upper (D 7) (R 7) [36,72,129,384,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23232 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23233 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 74 133 392 50 96 83 147 275), lower := (rows 37 74 133 392 50 96 64 128 256), losses := [] }

theorem u23233 : Upper (D 7) (R 7) [36,72,129,384,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23234 : Route 9 := (fun mask => (mask,id))

def c23234 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23234 : Upper (D 7) (R 7) [36,72,129,384,65,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384,65,2] 13 (by decide) (choices 1) [2,16,32] r23234 c23234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7345
  · exact u7346
  · exact u7347

def r23235 : Route 9 := (fun mask => (mask,id))

def c23235 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23235 : Upper (D 7) (R 7) [36,72,129,384,65,16] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384,65,16] 13 (by decide) (choices 1) [2,32] r23235 c23235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7348
  · exact u7349

def b23236 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 37, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 74 133 392 112 33 82 146 274), lower := (rows 37 74 133 392 112 33 64 128 256), losses := [] }

theorem u23236 : Upper (D 7) (R 7) [36,72,129,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23237 : Route 9 := (fun mask => (mask,id))

def c23237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23237 : Upper (D 7) (R 7) [36,72,129,384,96,2] 13 := by
  apply FastRouting.sound _ _ [36,72,129,384,96,2] 13 (by decide) (choices 1) [1,2,16] r23237 c23237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7350
  · exact u7351
  · exact u7352

def b23238 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 133 392 112 48 67 131 259), lower := (rows 37 74 133 392 112 48 64 128 256), losses := [] }

theorem u23238 : Upper (D 7) (R 7) [36,72,129,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23238 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23239 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(3,6),(4,6)], upper := (rows 37 74 134 137 50 33 336 464 336), lower := (rows 37 74 134 137 50 33 64 128 256), losses := [] }

theorem u23239 : Upper (D 7) (R 7) [36,72,130,129,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23240 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 134 137 50 48 321 449 321), lower := (rows 37 74 134 137 50 48 64 128 256), losses := [] }

theorem u23240 : Upper (D 7) (R 7) [36,72,130,129,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23240 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23241 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 74 134 137 50 96 337 401 273), lower := (rows 37 74 134 137 50 96 64 128 256), losses := [] }

theorem u23241 : Upper (D 7) (R 7) [36,72,130,129,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23242 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 3, region := 370, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 74 134 137 50 288 81 209 337), lower := (rows 37 74 134 137 50 288 64 128 256), losses := [] }

theorem u23242 : Upper (D 7) (R 7) [36,72,130,129,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23242 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23243 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 134 137 112 33 338 402 274), lower := (rows 37 74 134 137 112 33 64 128 256), losses := [] }

theorem u23243 : Upper (D 7) (R 7) [36,72,130,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23244 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 48, targets := 129 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 37 74 134 137 112 34 337 401 273), lower := (rows 37 74 134 137 112 34 64 128 256), losses := [] }

theorem u23244 : Upper (D 7) (R 7) [36,72,130,129,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23245 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 134 137 112 48 323 387 259), lower := (rows 37 74 134 137 112 48 64 128 256), losses := [] }

theorem u23245 : Upper (D 7) (R 7) [36,72,130,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23245 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23246 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 3, region := 370, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 74 134 137 112 288 83 147 275), lower := (rows 37 74 134 137 112 288 64 128 256), losses := [] }

theorem u23246 : Upper (D 7) (R 7) [36,72,130,129,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23246 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23247 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 37 74 134 137 273 34 112 240 368), lower := (rows 37 74 134 137 273 34 64 128 256), losses := [] }

theorem u23247 : Upper (D 7) (R 7) [36,72,130,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23248 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 3, region := 370, targets := 128 }], pairs := [(0,7),(1,7),(4,7)], upper := (rows 37 74 134 137 273 48 98 226 354), lower := (rows 37 74 134 137 273 48 64 128 256), losses := [] }

theorem u23248 : Upper (D 7) (R 7) [36,72,130,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23248 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23249 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 3, region := 370, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(4,7)], upper := (rows 37 74 134 137 273 96 114 178 306), lower := (rows 37 74 134 137 273 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 16 98 64 128 256), good := (rows 45 104 173 137 273 96 96 128 256) }] }

theorem u23249 : Upper (D 7) (R 7) [36,72,130,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23250 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 134 137 304 33 82 210 338), lower := (rows 37 74 134 137 304 33 64 128 256), losses := [] }

theorem u23250 : Upper (D 7) (R 7) [36,72,130,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23251 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 37 74 134 137 304 34 81 209 337), lower := (rows 37 74 134 137 304 34 64 128 256), losses := [] }

theorem u23251 : Upper (D 7) (R 7) [36,72,130,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23252 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 37 74 134 137 304 48 67 195 323), lower := (rows 37 74 134 137 304 48 64 128 256), losses := [] }

theorem u23252 : Upper (D 7) (R 7) [36,72,130,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23252 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23253 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 3, region := 370, targets := 128 }], pairs := [(0,1),(0,7),(1,7),(4,7)], upper := (rows 37 74 134 137 304 96 83 147 275), lower := (rows 37 74 134 137 304 96 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 16 98 64 128 256), good := (rows 45 104 173 137 304 96 96 128 256) }] }

theorem u23253 : Upper (D 7) (R 7) [36,72,130,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23254 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 57, targets := 64 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,6),(4,6)], upper := (rows 37 74 134 152 50 33 321 449 321), lower := (rows 37 74 134 152 50 33 64 128 256), losses := [] }

theorem u23254 : Upper (D 7) (R 7) [36,72,130,144,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23255 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 74 134 152 50 96 321 385 257), lower := (rows 37 74 134 152 50 96 64 128 256), losses := [] }

theorem u23255 : Upper (D 7) (R 7) [36,72,130,144,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23256 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 2, region := 353, targets := 2 }], pairs := [(0,1),(0,7),(4,7)], upper := (rows 37 74 134 152 50 288 65 193 321), lower := (rows 37 74 134 152 50 288 64 128 256), losses := [] }

theorem u23256 : Upper (D 7) (R 7) [36,72,130,144,34,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23256 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23257 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(4,7)], upper := (rows 37 74 134 152 273 33 98 226 354), lower := (rows 37 74 134 152 273 33 64 128 256), losses := [] }

theorem u23257 : Upper (D 7) (R 7) [36,72,130,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23258 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 37 74 134 152 273 34 97 225 353), lower := (rows 37 74 134 152 273 34 64 128 256), losses := [] }

theorem u23258 : Upper (D 7) (R 7) [36,72,130,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23259 : Route 9 := (fun mask => (mask,id))

def c23259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23259 : Upper (D 7) (R 7) [36,72,130,144,257,64] 13 := by
  apply FastRouting.sound _ _ [36,72,130,144,257,64] 13 (by decide) (choices 1) [1,2,32] r23259 c23259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7353
  · exact u7354
  · exact u7355

def b23260 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 2, region := 33, targets := 2 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(4,7)], upper := (rows 37 74 134 152 274 33 97 225 353), lower := (rows 37 74 134 152 274 33 64 128 256), losses := [] }

theorem u23260 : Upper (D 7) (R 7) [36,72,130,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23260 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23261 : Route 9 := (fun mask => (mask,id))

def c23261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23261 : Upper (D 7) (R 7) [36,72,130,144,258,64] 13 := by
  apply FastRouting.sound _ _ [36,72,130,144,258,64] 13 (by decide) (choices 1) [1,32] r23261 c23261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7356
  · exact u7357

def b23262 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(4,7)], upper := (rows 37 74 134 152 304 33 67 195 323), lower := (rows 37 74 134 152 304 33 64 128 256), losses := [] }

theorem u23262 : Upper (D 7) (R 7) [36,72,130,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23262 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23263 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7),(3,1),(4,1),(4,7)], upper := (rows 37 74 134 152 304 34 65 193 321), lower := (rows 37 74 134 152 304 34 64 128 256), losses := [] }

theorem u23263 : Upper (D 7) (R 7) [36,72,130,144,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23264 : Route 9 := (fun mask => (mask,id))

def c23264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23264 : Upper (D 7) (R 7) [36,72,130,144,288,64] 13 := by
  apply FastRouting.sound _ _ [36,72,130,144,288,64] 13 (by decide) (choices 1) [1,2] r23264 c23264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7358
  · exact u7359

def b23265 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 134 168 81 33 338 402 274), lower := (rows 37 74 134 168 81 33 64 128 256), losses := [] }

theorem u23265 : Upper (D 7) (R 7) [36,72,130,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23265 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23266 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 37 74 134 168 81 34 337 401 273), lower := (rows 37 74 134 168 81 34 64 128 256), losses := [] }

theorem u23266 : Upper (D 7) (R 7) [36,72,130,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23267 : Route 9 := (fun mask => (mask,id))

def c23267 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u23267 : Upper (D 7) (R 7) [36,72,130,160,65,16] 13 := by
  apply FastRouting.sound _ _ [36,72,130,160,65,16] 13 (by decide) (choices 1) [1,2,256] r23267 c23267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7360
  · exact u7361
  · exact u7362

def r23268 : Route 9 := (fun mask => (mask,id))

def c23268 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23268 : Upper (D 7) (R 7) [36,72,130,160,65,256] 13 := by
  apply FastRouting.sound _ _ [36,72,130,160,65,256] 13 (by decide) (choices 1) [1,2,16] r23268 c23268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7363
  · exact u7364
  · exact u7365

def b23269 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 134 168 273 33 82 210 338), lower := (rows 37 74 134 168 273 33 64 128 256), losses := [] }

theorem u23269 : Upper (D 7) (R 7) [36,72,130,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23269 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23270 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 37 74 134 168 273 34 81 209 337), lower := (rows 37 74 134 168 273 34 64 128 256), losses := [] }

theorem u23270 : Upper (D 7) (R 7) [36,72,130,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23271 : Route 9 := (fun mask => (mask,id))

def c23271 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23271 : Upper (D 7) (R 7) [36,72,130,160,257,16] 13 := by
  apply FastRouting.sound _ _ [36,72,130,160,257,16] 13 (by decide) (choices 1) [1,2] r23271 c23271
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7366
  · exact u7367

def b23272 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,1),(0,7),(3,0),(4,7)], upper := (rows 37 74 134 168 273 96 83 147 275), lower := (rows 37 74 134 168 273 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 98 64 128 256), good := (rows 44 106 174 168 272 96 96 128 256) },{ target := 1, region := (rows 5 0 4 12 16 98 64 128 256), good := (rows 45 104 173 168 273 96 96 128 256) }] }

theorem u23272 : Upper (D 7) (R 7) [36,72,130,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23272 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23273 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 134 168 274 33 81 209 337), lower := (rows 37 74 134 168 274 33 64 128 256), losses := [] }

theorem u23273 : Upper (D 7) (R 7) [36,72,130,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23274 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 369, targets := 128 },{ cop := 0, region := 200, targets := 2 }], pairs := [(0,7),(3,1),(4,7)], upper := (rows 37 74 134 168 274 48 65 193 321), lower := (rows 37 74 134 168 274 48 64 128 256), losses := [] }

theorem u23274 : Upper (D 7) (R 7) [36,72,130,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23274 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23275 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,1),(0,7),(3,0),(4,7)], upper := (rows 37 74 134 168 274 96 81 145 273), lower := (rows 37 74 134 168 274 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 98 64 128 256), good := (rows 44 106 174 168 306 96 96 128 256) },{ target := 1, region := (rows 5 0 4 12 16 98 64 128 256), good := (rows 45 104 173 168 304 96 96 128 256) }] }

theorem u23275 : Upper (D 7) (R 7) [36,72,130,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23275 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23276 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 134 168 336 33 83 147 275), lower := (rows 37 74 134 168 336 33 64 128 256), losses := [] }

theorem u23276 : Upper (D 7) (R 7) [36,72,130,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23276 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23277 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(3,1),(3,6),(4,1)], upper := (rows 37 74 134 168 336 34 81 145 273), lower := (rows 37 74 134 168 336 34 64 128 256), losses := [] }

theorem u23277 : Upper (D 7) (R 7) [36,72,130,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23277 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r23278 : Route 9 := (fun mask => (mask,id))

def c23278 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23278 : Upper (D 7) (R 7) [36,72,130,160,320,16] 13 := by
  apply FastRouting.sound _ _ [36,72,130,160,320,16] 13 (by decide) (choices 1) [1,2] r23278 c23278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7368
  · exact u7369

def b23279 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 49, targets := 192 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 37 74 134 265 19 48 224 224 480), lower := (rows 37 74 134 265 19 48 64 128 256), losses := [] }

theorem u23279 : Upper (D 7) (R 7) [36,72,130,257,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23279 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u23279
end Delivery.IrregularNine14.P07
