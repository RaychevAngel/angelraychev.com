import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0052

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r14280 : Route 9 := (fun mask => (mask,id))

def c14280 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14280 : Upper (D 6) (R 6) [10,48,129,68,258,1] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,258,1] 13 (by decide) (choices 1) [4,32] r14280 c14280
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3129
  · exact u3130

def r14281 : Route 9 := (fun mask => (mask,id))

def c14281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14281 : Upper (D 6) (R 6) [10,48,129,68,258,4] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,258,4] 13 (by decide) (choices 1) [1,32] r14281 c14281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3131
  · exact u3132

def r14282 : Route 9 := (fun mask => (mask,id))

def c14282 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14282 : Upper (D 6) (R 6) [10,48,129,68,258,64] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,258,64] 13 (by decide) (choices 1) [1,4,32] r14282 c14282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3133
  · exact u3134
  · exact u3135

def r14283 : Route 9 := (fun mask => (mask,id))

def c14283 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14283 : Upper (D 6) (R 6) [10,48,129,68,260,1] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,260,1] 13 (by decide) (choices 1) [2,32] r14283 c14283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3136
  · exact u3137

def b14284 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 133 76 276 34 97 225 353), lower := (rows 11 50 133 76 276 34 64 128 256), losses := [] }

theorem u14284 : Upper (D 6) (R 6) [10,48,129,68,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14285 : Route 9 := (fun mask => (mask,id))

def c14285 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14285 : Upper (D 6) (R 6) [10,48,129,68,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,260,64] 13 (by decide) (choices 1) [1,2,32] r14285 c14285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3138
  · exact u3139
  · exact u3140

def r14286 : Route 9 := (fun mask => (mask,id))

def c14286 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14286 : Upper (D 6) (R 6) [10,48,129,68,320,1] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,320,1] 13 (by decide) (choices 1) [2,4,32] r14286 c14286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3141
  · exact u3142
  · exact u3143

def b14287 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 133 76 336 34 101 165 293), lower := (rows 11 50 133 76 336 34 64 128 256), losses := [] }

theorem u14287 : Upper (D 6) (R 6) [10,48,129,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14288 : Route 9 := (fun mask => (mask,id))

def c14288 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14288 : Upper (D 6) (R 6) [10,48,129,68,320,4] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,320,4] 13 (by decide) (choices 1) [1,2,32] r14288 c14288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3144
  · exact u3145
  · exact u3146

def b14289 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 133 104 273 34 68 196 324), lower := (rows 11 50 133 104 273 34 64 128 256), losses := [] }

theorem u14289 : Upper (D 6) (R 6) [10,48,129,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14290 : Route 9 := (fun mask => (mask,id))

def c14290 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14290 : Upper (D 6) (R 6) [10,48,129,96,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,129,96,257,4] 13 (by decide) (choices 1) [2,4] r14290 c14290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3147
  · exact u3148

def b14291 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 50 133 104 273 96 70 134 262), lower := (rows 11 50 133 104 273 96 64 128 256), losses := [] }

theorem u14291 : Upper (D 6) (R 6) [10,48,129,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14292 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 50 133 104 276 33 70 198 326), lower := (rows 11 50 133 104 276 33 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 37 64 128 256), good := (rows 43 50 161 104 306 33 64 128 256) }] }

theorem u14292 : Upper (D 6) (R 6) [10,48,129,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14293 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 133 104 276 34 69 197 325), lower := (rows 11 50 133 104 276 34 64 128 256), losses := [] }

theorem u14293 : Upper (D 6) (R 6) [10,48,129,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14294 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 133 104 276 36 67 195 323), lower := (rows 11 50 133 104 276 36 64 128 256), losses := [] }

theorem u14294 : Upper (D 6) (R 6) [10,48,129,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14295 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 50 133 104 276 96 71 135 263), lower := (rows 11 50 133 104 276 96 64 128 256), losses := [] }

theorem u14295 : Upper (D 6) (R 6) [10,48,129,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14296 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 133 265 84 34 100 228 356), lower := (rows 11 50 133 265 84 34 64 128 256), losses := [] }

theorem u14296 : Upper (D 6) (R 6) [10,48,129,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14297 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 2, region := 114, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 133 265 84 36 98 226 354), lower := (rows 11 50 133 265 84 36 64 128 256), losses := [] }

theorem u14297 : Upper (D 6) (R 6) [10,48,129,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14298 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 133 265 84 96 102 166 294), lower := (rows 11 50 133 265 84 96 64 128 256), losses := [] }

theorem u14298 : Upper (D 6) (R 6) [10,48,129,257,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14299 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 133 268 81 34 100 228 356), lower := (rows 11 50 133 268 81 34 64 128 256), losses := [] }

theorem u14299 : Upper (D 6) (R 6) [10,48,129,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14300 : Route 9 := (fun mask => (mask,id))

def c14300 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14300 : Upper (D 6) (R 6) [10,48,129,260,65,4] 13 := by
  apply FastRouting.sound _ _ [10,48,129,260,65,4] 13 (by decide) (choices 1) [2,32] r14300 c14300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3149
  · exact u3150

def b14301 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 133 268 81 96 102 166 294), lower := (rows 11 50 133 268 81 96 64 128 256), losses := [] }

theorem u14301 : Upper (D 6) (R 6) [10,48,129,260,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14302 : Route 9 := (fun mask => (mask,id))

def c14302 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14302 : Upper (D 6) (R 6) [10,48,129,260,66,1] 13 := by
  apply FastRouting.sound _ _ [10,48,129,260,66,1] 13 (by decide) (choices 1) [4,32] r14302 c14302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3151
  · exact u3152

def r14303 : Route 9 := (fun mask => (mask,id))

def c14303 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14303 : Upper (D 6) (R 6) [10,48,129,260,66,4] 13 := by
  apply FastRouting.sound _ _ [10,48,129,260,66,4] 13 (by decide) (choices 1) [1,32] r14303 c14303
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3153
  · exact u3154

def b14304 : PairBound 9 := { available := 37, camps := [{ cop := 5, region := 18, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 133 268 82 96 101 165 293), lower := (rows 11 50 133 268 82 96 64 128 256), losses := [] }

theorem u14304 : Upper (D 6) (R 6) [10,48,129,260,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14305 : Route 9 := (fun mask => (mask,id))

def c14305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14305 : Upper (D 6) (R 6) [10,48,129,260,68,1] 13 := by
  apply FastRouting.sound _ _ [10,48,129,260,68,1] 13 (by decide) (choices 1) [2,32] r14305 c14305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3155
  · exact u3156

def b14306 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 133 268 84 34 97 225 353), lower := (rows 11 50 133 268 84 34 64 128 256), losses := [] }

theorem u14306 : Upper (D 6) (R 6) [10,48,129,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14307 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 133 268 84 96 99 163 291), lower := (rows 11 50 133 268 84 96 64 128 256), losses := [] }

theorem u14307 : Upper (D 6) (R 6) [10,48,129,260,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14308 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 133 296 81 34 68 196 324), lower := (rows 11 50 133 296 81 34 64 128 256), losses := [] }

theorem u14308 : Upper (D 6) (R 6) [10,48,129,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14309 : Route 9 := (fun mask => (mask,id))

def c14309 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14309 : Upper (D 6) (R 6) [10,48,129,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,48,129,288,65,4] 13 (by decide) (choices 1) [2,4] r14309 c14309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3157
  · exact u3158

def b14310 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 133 296 81 96 70 134 262), lower := (rows 11 50 133 296 81 96 64 128 256), losses := [] }

theorem u14310 : Upper (D 6) (R 6) [10,48,129,288,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14311 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 50 133 296 84 33 70 198 326), lower := (rows 11 50 133 296 84 33 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 37 64 128 256), good := (rows 43 50 161 296 114 33 64 128 256) }] }

theorem u14311 : Upper (D 6) (R 6) [10,48,129,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14312 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 133 296 84 34 69 197 325), lower := (rows 11 50 133 296 84 34 64 128 256), losses := [] }

theorem u14312 : Upper (D 6) (R 6) [10,48,129,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14313 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 133 296 84 36 67 195 323), lower := (rows 11 50 133 296 84 36 64 128 256), losses := [] }

theorem u14313 : Upper (D 6) (R 6) [10,48,129,288,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14314 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 133 296 84 96 71 135 263), lower := (rows 11 50 133 296 84 96 64 128 256), losses := [] }

theorem u14314 : Upper (D 6) (R 6) [10,48,129,288,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14315 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 50, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 11 50 133 328 22 33 100 228 356), lower := (rows 11 50 133 328 22 33 64 128 256), losses := [] }

theorem u14315 : Upper (D 6) (R 6) [10,48,129,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14316 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 50 133 328 22 36 97 225 353), lower := (rows 11 50 133 328 22 36 64 128 256), losses := [] }

theorem u14316 : Upper (D 6) (R 6) [10,48,129,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14316 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14317 : Route 9 := (fun mask => (mask,id))

def c14317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14317 : Upper (D 6) (R 6) [10,48,129,320,6,64] 13 := by
  apply FastRouting.sound _ _ [10,48,129,320,6,64] 13 (by decide) (choices 1) [1,4,32] r14317 c14317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3159
  · exact u3160
  · exact u3161

def b14318 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 133 328 81 34 100 164 292), lower := (rows 11 50 133 328 81 34 64 128 256), losses := [] }

theorem u14318 : Upper (D 6) (R 6) [10,48,129,320,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14319 : Route 9 := (fun mask => (mask,id))

def c14319 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14319 : Upper (D 6) (R 6) [10,48,129,320,65,4] 13 := by
  apply FastRouting.sound _ _ [10,48,129,320,65,4] 13 (by decide) (choices 1) [2,4,32] r14319 c14319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3162
  · exact u3163
  · exact u3164

def b14320 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(1,2),(1,6),(2,6)], upper := (rows 11 50 133 328 84 33 102 166 294), lower := (rows 11 50 133 328 84 33 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 37 64 128 256), good := (rows 43 50 161 328 114 33 64 128 256) },{ target := 6, region := (rows 1 18 37 8 16 37 0 147 275), good := (rows 431 438 421 264 438 421 0 128 256) }] }

theorem u14320 : Upper (D 6) (R 6) [10,48,129,320,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14321 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 133 328 84 34 101 165 293), lower := (rows 11 50 133 328 84 34 64 128 256), losses := [] }

theorem u14321 : Upper (D 6) (R 6) [10,48,129,320,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14322 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 133 328 84 36 99 163 291), lower := (rows 11 50 133 328 84 36 64 128 256), losses := [] }

theorem u14322 : Upper (D 6) (R 6) [10,48,129,320,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14323 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 452, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 134 44 81 33 324 452 324), lower := (rows 11 50 134 44 81 33 64 128 256), losses := [] }

theorem u14323 : Upper (D 6) (R 6) [10,48,130,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14324 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 134 44 81 36 321 449 321), lower := (rows 11 50 134 44 81 36 64 128 256), losses := [] }

theorem u14324 : Upper (D 6) (R 6) [10,48,130,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14325 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 134 44 81 96 325 389 261), lower := (rows 11 50 134 44 81 96 64 128 256), losses := [] }

theorem u14325 : Upper (D 6) (R 6) [10,48,130,36,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14326 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 50 134 44 81 288 69 197 325), lower := (rows 11 50 134 44 81 288 64 128 256), losses := [] }

theorem u14326 : Upper (D 6) (R 6) [10,48,130,36,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14326 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14327 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 134 44 84 33 321 449 321), lower := (rows 11 50 134 44 84 33 64 128 256), losses := [] }

theorem u14327 : Upper (D 6) (R 6) [10,48,130,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14328 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 134 44 84 96 321 385 257), lower := (rows 11 50 134 44 84 96 64 128 256), losses := [] }

theorem u14328 : Upper (D 6) (R 6) [10,48,130,36,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14329 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 50 134 44 84 288 65 193 321), lower := (rows 11 50 134 44 84 288 64 128 256), losses := [] }

theorem u14329 : Upper (D 6) (R 6) [10,48,130,36,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14329 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14330 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 134 44 273 33 68 196 324), lower := (rows 11 50 134 44 273 33 64 128 256), losses := [] }

theorem u14330 : Upper (D 6) (R 6) [10,48,130,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14331 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 134 44 273 36 65 193 321), lower := (rows 11 50 134 44 273 36 64 128 256), losses := [] }

theorem u14331 : Upper (D 6) (R 6) [10,48,130,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14331 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14332 : Route 9 := (fun mask => (mask,id))

def c14332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14332 : Upper (D 6) (R 6) [10,48,130,36,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,130,36,257,64] 13 (by decide) (choices 1) [1,4] r14332 c14332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3165
  · exact u3166

def b14333 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 134 44 276 33 65 193 321), lower := (rows 11 50 134 44 276 33 64 128 256), losses := [] }

theorem u14333 : Upper (D 6) (R 6) [10,48,130,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14334 : Route 9 := (fun mask => (mask,id))

def c14334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14334 : Upper (D 6) (R 6) [10,48,130,36,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,130,36,260,64] 13 (by decide) (choices 1) [1] r14334 c14334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u3167

def b14335 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 50 134 44 336 33 69 197 325), lower := (rows 11 50 134 44 336 33 64 128 256), losses := [] }

theorem u14335 : Upper (D 6) (R 6) [10,48,130,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14335 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14336 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 134 44 336 36 65 193 321), lower := (rows 11 50 134 44 336 36 64 128 256), losses := [] }

theorem u14336 : Upper (D 6) (R 6) [10,48,130,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14337 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 134 44 336 96 69 133 261), lower := (rows 11 50 134 44 336 96 64 128 256), losses := [] }

theorem u14337 : Upper (D 6) (R 6) [10,48,130,36,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14337 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14338 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 134 73 84 33 356 420 292), lower := (rows 11 50 134 73 84 33 64 128 256), losses := [] }

theorem u14338 : Upper (D 6) (R 6) [10,48,130,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14339 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 134 73 84 36 353 417 289), lower := (rows 11 50 134 73 84 36 64 128 256), losses := [] }

theorem u14339 : Upper (D 6) (R 6) [10,48,130,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u14339
end Delivery.IrregularNine14.P06
