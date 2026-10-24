import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0052
import IrregularNine14P06C0053

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r14340 : Route 9 := (fun mask => (mask,id))

def c14340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14340 : Upper (D 6) (R 6) [10,48,130,65,68,256] 13 := by
  apply FastRouting.sound _ _ [10,48,130,65,68,256] 13 (by decide) (choices 1) [1,4,32] r14340 c14340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3168
  · exact u3169
  · exact u3170

def r14341 : Route 9 := (fun mask => (mask,id))

def c14341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14341 : Upper (D 6) (R 6) [10,48,130,65,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,130,65,257,4] 13 (by decide) (choices 1) [4,32] r14341 c14341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3171
  · exact u3172

def b14342 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 1, region := 132, targets := 64 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 11 50 134 73 273 96 100 164 292), lower := (rows 11 50 134 73 273 96 64 128 256), losses := [] }

theorem u14342 : Upper (D 6) (R 6) [10,48,130,65,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14343 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 134 73 276 33 100 228 356), lower := (rows 11 50 134 73 276 33 64 128 256), losses := [] }

theorem u14343 : Upper (D 6) (R 6) [10,48,130,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14344 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 134 73 276 36 97 225 353), lower := (rows 11 50 134 73 276 36 64 128 256), losses := [] }

theorem u14344 : Upper (D 6) (R 6) [10,48,130,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14345 : Route 9 := (fun mask => (mask,id))

def c14345 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14345 : Upper (D 6) (R 6) [10,48,130,65,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,130,65,260,64] 13 (by decide) (choices 1) [1,4,32] r14345 c14345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3173
  · exact u3174
  · exact u3175

def b14346 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 134 73 336 33 100 164 292), lower := (rows 11 50 134 73 336 33 64 128 256), losses := [] }

theorem u14346 : Upper (D 6) (R 6) [10,48,130,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14347 : Route 9 := (fun mask => (mask,id))

def c14347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14347 : Upper (D 6) (R 6) [10,48,130,65,320,4] 13 := by
  apply FastRouting.sound _ _ [10,48,130,65,320,4] 13 (by decide) (choices 1) [1,4,32] r14347 c14347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3176
  · exact u3177
  · exact u3178

def b14348 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 134 76 21 33 352 480 352), lower := (rows 11 50 134 76 21 33 64 128 256), losses := [] }

theorem u14348 : Upper (D 6) (R 6) [10,48,130,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14349 : Route 9 := (fun mask => (mask,id))

def c14349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u14349 : Upper (D 6) (R 6) [10,48,130,68,5,64] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,5,64] 13 (by decide) (choices 1) [1,32,256] r14349 c14349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3179
  · exact u3180
  · exact u3181

def b14350 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 360, targets := 2 },{ cop := 4, region := 354, targets := 4 }], pairs := [(1,2),(3,1)], upper := (rows 11 50 134 76 21 288 97 225 353), lower := (rows 11 50 134 76 21 288 64 128 256), losses := [] }

theorem u14350 : Upper (D 6) (R 6) [10,48,130,68,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14350 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14351 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 134 76 81 33 356 420 292), lower := (rows 11 50 134 76 81 33 64 128 256), losses := [] }

theorem u14351 : Upper (D 6) (R 6) [10,48,130,68,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14352 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 11 50 134 76 81 36 353 417 289), lower := (rows 11 50 134 76 81 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 65 129 257), good := (rows 505 48 164 108 465 36 64 128 256) }] }

theorem u14352 : Upper (D 6) (R 6) [10,48,130,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14353 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 50 134 76 81 288 101 165 293), lower := (rows 11 50 134 76 81 288 64 128 256), losses := [] }

theorem u14353 : Upper (D 6) (R 6) [10,48,130,68,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14353 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14354 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 134 76 273 33 100 228 356), lower := (rows 11 50 134 76 273 33 64 128 256), losses := [] }

theorem u14354 : Upper (D 6) (R 6) [10,48,130,68,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14355 : Route 9 := (fun mask => (mask,id))

def c14355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14355 : Upper (D 6) (R 6) [10,48,130,68,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,257,4] 13 (by decide) (choices 1) [1,32] r14355 c14355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3182
  · exact u3183

def r14356 : Route 9 := (fun mask => (mask,id))

def c14356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14356 : Upper (D 6) (R 6) [10,48,130,68,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,257,64] 13 (by decide) (choices 1) [1,4,32] r14356 c14356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3184
  · exact u3185
  · exact u3186

def r14357 : Route 9 := (fun mask => (mask,id))

def c14357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14357 : Upper (D 6) (R 6) [10,48,130,68,260,1] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,260,1] 13 (by decide) (choices 1) [1,32] r14357 c14357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3187
  · exact u3188

def r14358 : Route 9 := (fun mask => (mask,id))

def c14358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14358 : Upper (D 6) (R 6) [10,48,130,68,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,260,64] 13 (by decide) (choices 1) [1,32] r14358 c14358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3189
  · exact u3190

def r14359 : Route 9 := (fun mask => (mask,id))

def c14359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14359 : Upper (D 6) (R 6) [10,48,130,68,320,1] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,320,1] 13 (by decide) (choices 1) [1,4,32] r14359 c14359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3191
  · exact u3192
  · exact u3193

def r14360 : Route 9 := (fun mask => (mask,id))

def c14360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14360 : Upper (D 6) (R 6) [10,48,130,68,320,4] 13 := by
  apply FastRouting.sound _ _ [10,48,130,68,320,4] 13 (by decide) (choices 1) [1,32] r14360 c14360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3194
  · exact u3195

def b14361 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 134 104 273 33 68 196 324), lower := (rows 11 50 134 104 273 33 64 128 256), losses := [] }

theorem u14361 : Upper (D 6) (R 6) [10,48,130,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14362 : Route 9 := (fun mask => (mask,id))

def c14362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14362 : Upper (D 6) (R 6) [10,48,130,96,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,130,96,257,4] 13 (by decide) (choices 1) [1,4] r14362 c14362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3196
  · exact u3197

def b14363 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 50 134 104 273 96 69 133 261), lower := (rows 11 50 134 104 273 96 64 128 256), losses := [] }

theorem u14363 : Upper (D 6) (R 6) [10,48,130,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14364 : Route 9 := (fun mask => (mask,id))

def c14364 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14364 : Upper (D 6) (R 6) [10,48,130,96,260,1] 13 := by
  apply FastRouting.sound _ _ [10,48,130,96,260,1] 13 (by decide) (choices 1) [1,4] r14364 c14364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3198
  · exact u3199

def b14365 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 134 104 276 36 65 193 321), lower := (rows 11 50 134 104 276 36 64 128 256), losses := [] }

theorem u14365 : Upper (D 6) (R 6) [10,48,130,96,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14366 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 50 134 104 276 96 69 133 261), lower := (rows 11 50 134 104 276 96 64 128 256), losses := [] }

theorem u14366 : Upper (D 6) (R 6) [10,48,130,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14367 : Route 9 := (fun mask => (mask,id))

def c14367 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14367 : Upper (D 6) (R 6) [10,48,130,257,65,4] 13 := by
  apply FastRouting.sound _ _ [10,48,130,257,65,4] 13 (by decide) (choices 1) [4,32] r14367 c14367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3200
  · exact u3201

def b14368 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 134 265 81 96 100 164 292), lower := (rows 11 50 134 265 81 96 64 128 256), losses := [] }

theorem u14368 : Upper (D 6) (R 6) [10,48,130,257,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14369 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 134 265 84 33 100 228 356), lower := (rows 11 50 134 265 84 33 64 128 256), losses := [] }

theorem u14369 : Upper (D 6) (R 6) [10,48,130,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14370 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 134 265 84 36 97 225 353), lower := (rows 11 50 134 265 84 36 64 128 256), losses := [] }

theorem u14370 : Upper (D 6) (R 6) [10,48,130,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14371 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 134 265 84 96 101 165 293), lower := (rows 11 50 134 265 84 96 64 128 256), losses := [] }

theorem u14371 : Upper (D 6) (R 6) [10,48,130,257,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14372 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 50 134 268 21 33 96 224 352), lower := (rows 11 50 134 268 21 33 64 128 256), losses := [] }

theorem u14372 : Upper (D 6) (R 6) [10,48,130,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14373 : Route 9 := (fun mask => (mask,id))

def c14373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14373 : Upper (D 6) (R 6) [10,48,130,260,5,64] 13 := by
  apply FastRouting.sound _ _ [10,48,130,260,5,64] 13 (by decide) (choices 1) [1,32] r14373 c14373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3202
  · exact u3203

def b14374 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 134 268 81 33 100 228 356), lower := (rows 11 50 134 268 81 33 64 128 256), losses := [] }

theorem u14374 : Upper (D 6) (R 6) [10,48,130,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14375 : Route 9 := (fun mask => (mask,id))

def c14375 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14375 : Upper (D 6) (R 6) [10,48,130,260,65,4] 13 := by
  apply FastRouting.sound _ _ [10,48,130,260,65,4] 13 (by decide) (choices 1) [1,32] r14375 c14375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3204
  · exact u3205

def b14376 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 134 268 81 96 101 165 293), lower := (rows 11 50 134 268 81 96 64 128 256), losses := [] }

theorem u14376 : Upper (D 6) (R 6) [10,48,130,260,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14377 : Route 9 := (fun mask => (mask,id))

def c14377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14377 : Upper (D 6) (R 6) [10,48,130,260,68,1] 13 := by
  apply FastRouting.sound _ _ [10,48,130,260,68,1] 13 (by decide) (choices 1) [1,32] r14377 c14377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3206
  · exact u3207

def b14378 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 134 268 84 96 97 161 289), lower := (rows 11 50 134 268 84 96 64 128 256), losses := [] }

theorem u14378 : Upper (D 6) (R 6) [10,48,130,260,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14379 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(2,5),(4,5)], upper := (rows 11 50 134 296 81 33 68 196 324), lower := (rows 11 50 134 296 81 33 64 128 256), losses := [] }

theorem u14379 : Upper (D 6) (R 6) [10,48,130,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14380 : Route 9 := (fun mask => (mask,id))

def c14380 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14380 : Upper (D 6) (R 6) [10,48,130,288,65,4] 13 := by
  apply FastRouting.sound _ _ [10,48,130,288,65,4] 13 (by decide) (choices 1) [1,4] r14380 c14380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3208
  · exact u3209

def b14381 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 134 296 81 96 69 133 261), lower := (rows 11 50 134 296 81 96 64 128 256), losses := [] }

theorem u14381 : Upper (D 6) (R 6) [10,48,130,288,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14382 : Route 9 := (fun mask => (mask,id))

def c14382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14382 : Upper (D 6) (R 6) [10,48,130,288,68,1] 13 := by
  apply FastRouting.sound _ _ [10,48,130,288,68,1] 13 (by decide) (choices 1) [1,4] r14382 c14382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3210
  · exact u3211

def b14383 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 50 134 296 84 36 65 193 321), lower := (rows 11 50 134 296 84 36 64 128 256), losses := [] }

theorem u14383 : Upper (D 6) (R 6) [10,48,130,288,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14384 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 134 296 84 96 69 133 261), lower := (rows 11 50 134 296 84 96 64 128 256), losses := [] }

theorem u14384 : Upper (D 6) (R 6) [10,48,130,288,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14385 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 134 328 21 33 100 228 356), lower := (rows 11 50 134 328 21 33 64 128 256), losses := [] }

theorem u14385 : Upper (D 6) (R 6) [10,48,130,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14386 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 134 328 21 36 97 225 353), lower := (rows 11 50 134 328 21 36 64 128 256), losses := [] }

theorem u14386 : Upper (D 6) (R 6) [10,48,130,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14387 : Route 9 := (fun mask => (mask,id))

def c14387 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14387 : Upper (D 6) (R 6) [10,48,130,320,5,64] 13 := by
  apply FastRouting.sound _ _ [10,48,130,320,5,64] 13 (by decide) (choices 1) [1,4,32] r14387 c14387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3212
  · exact u3213
  · exact u3214

def b14388 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 134 328 81 33 100 164 292), lower := (rows 11 50 134 328 81 33 64 128 256), losses := [] }

theorem u14388 : Upper (D 6) (R 6) [10,48,130,320,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14389 : Route 9 := (fun mask => (mask,id))

def c14389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14389 : Upper (D 6) (R 6) [10,48,130,320,65,4] 13 := by
  apply FastRouting.sound _ _ [10,48,130,320,65,4] 13 (by decide) (choices 1) [1,4,32] r14389 c14389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3215
  · exact u3216
  · exact u3217

def r14390 : Route 9 := (fun mask => (mask,id))

def c14390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14390 : Upper (D 6) (R 6) [10,48,130,320,68,1] 13 := by
  apply FastRouting.sound _ _ [10,48,130,320,68,1] 13 (by decide) (choices 1) [1,4,32] r14390 c14390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3218
  · exact u3219
  · exact u3220

def b14391 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 134 328 84 36 97 161 289), lower := (rows 11 50 134 328 84 36 64 128 256), losses := [] }

theorem u14391 : Upper (D 6) (R 6) [10,48,130,320,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14392 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 336, targets := 34 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 11 50 164 13 81 34 324 452 324), lower := (rows 11 50 164 13 81 34 64 128 256), losses := [] }

theorem u14392 : Upper (D 6) (R 6) [10,48,160,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14393 : PairBound 9 := { available := 322, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 50 164 13 81 36 322 450 322), lower := (rows 11 50 164 13 81 36 64 128 256), losses := [] }

theorem u14393 : Upper (D 6) (R 6) [10,48,160,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14394 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 164 13 81 96 326 390 262), lower := (rows 11 50 164 13 81 96 64 128 256), losses := [] }

theorem u14394 : Upper (D 6) (R 6) [10,48,160,5,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14395 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 50 164 13 81 288 70 198 326), lower := (rows 11 50 164 13 81 288 64 128 256), losses := [] }

theorem u14395 : Upper (D 6) (R 6) [10,48,160,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14395 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14396 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 164 13 84 33 322 450 322), lower := (rows 11 50 164 13 84 33 64 128 256), losses := [] }

theorem u14396 : Upper (D 6) (R 6) [10,48,160,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14397 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 164 13 84 34 321 449 321), lower := (rows 11 50 164 13 84 34 64 128 256), losses := [] }

theorem u14397 : Upper (D 6) (R 6) [10,48,160,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14398 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 164 13 84 96 323 387 259), lower := (rows 11 50 164 13 84 96 64 128 256), losses := [] }

theorem u14398 : Upper (D 6) (R 6) [10,48,160,5,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14399 : Route 9 := (fun mask => (mask,id))

def c14399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14399 : Upper (D 6) (R 6) [10,48,160,5,68,256] 13 := by
  apply FastRouting.sound _ _ [10,48,160,5,68,256] 13 (by decide) (choices 1) [1,2] r14399 c14399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3221
  · exact u3222

#print axioms u14399
end Delivery.IrregularNine14.P06
