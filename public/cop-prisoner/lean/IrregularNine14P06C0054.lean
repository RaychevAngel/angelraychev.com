import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0003

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3240 : Route 9 := (fun mask => (mask,id))

def c3240 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3240 : Upper (D 6) (R 6) [10,48,160,68,258,64,1] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,258,64,1] 13 (by decide) (choices 1) [1,4] r3240 c3240
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u226
  · exact u227

def b3241 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 50 164 76 274 96 68 129 257), lower := (rows 11 50 164 76 274 96 68 128 256), losses := [] }

theorem u3241 : Upper (D 6) (R 6) [10,48,160,68,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3242 : Route 9 := (fun mask => (mask,id))

def c3242 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3242 : Upper (D 6) (R 6) [10,48,160,68,260,1,1] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,260,1,1] 13 (by decide) (choices 1) [2,64] r3242 c3242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u228
  · exact u229

def r3243 : Route 9 := (fun mask => (mask,id))

def c3243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3243 : Upper (D 6) (R 6) [10,48,160,68,260,1,2] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,260,1,2] 13 (by decide) (choices 1) [1,64] r3243 c3243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u230
  · exact u231

def r3244 : Route 9 := (fun mask => (mask,id))

def c3244 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3244 : Upper (D 6) (R 6) [10,48,160,68,260,64,1] 13 := by
  apply FastRouting.sound _ _ [10,48,160,68,260,64,1] 13 (by decide) (choices 1) [1,2] r3244 c3244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u232
  · exact u233

def b3245 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 11 50 164 76 276 96 66 129 257), lower := (rows 11 50 164 76 276 96 66 128 256), losses := [] }

theorem u3245 : Upper (D 6) (R 6) [10,48,160,68,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3246 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 132, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 50 164 76 336 33 65 134 262), lower := (rows 11 50 164 76 336 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 38 8 80 32 64 131 259), good := (rows 398 438 164 92 336 420 464 128 256) }] }

theorem u3246 : Upper (D 6) (R 6) [10,48,160,68,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3247 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 164, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 50 164 76 336 33 66 133 261), lower := (rows 11 50 164 76 336 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 39 72 16 33 64 161 289), good := (rows 429 436 420 76 344 421 76 128 256) }] }

theorem u3247 : Upper (D 6) (R 6) [10,48,160,68,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3248 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 50 164 76 336 33 68 131 259), lower := (rows 11 50 164 76 336 33 68 128 256), losses := [] }

theorem u3248 : Upper (D 6) (R 6) [10,48,160,68,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3249 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 164 265 21 96 66 196 324), lower := (rows 11 50 164 265 21 96 66 128 256), losses := [] }

theorem u3249 : Upper (D 6) (R 6) [10,48,160,257,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3250 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 7, region := 100, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 164 265 21 96 68 194 322), lower := (rows 11 50 164 265 21 96 68 128 256), losses := [] }

theorem u3250 : Upper (D 6) (R 6) [10,48,160,257,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3251 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 115, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 164 268 82 33 65 196 324), lower := (rows 11 50 164 268 82 33 65 128 256), losses := [] }

theorem u3251 : Upper (D 6) (R 6) [10,48,160,260,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3252 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 2, region := 82, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 50 164 268 82 33 68 193 321), lower := (rows 11 50 164 268 82 33 68 128 256), losses := [] }

theorem u3252 : Upper (D 6) (R 6) [10,48,160,260,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3253 : PairBound 9 := { available := 66, camps := [], pairs := [(1,2),(4,1),(4,5)], upper := (rows 11 50 164 268 84 33 65 194 322), lower := (rows 11 50 164 268 84 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 20 97 97 128 256), good := (rows 105 112 244 284 116 97 97 128 256) },{ target := 2, region := (rows 1 18 0 8 16 97 97 147 275), good := (rows 491 498 224 264 498 481 481 128 256) },{ target := 5, region := (rows 1 2 4 8 20 0 97 131 259), good := (rows 459 466 212 284 84 449 449 128 256) }] }

theorem u3253 : Upper (D 6) (R 6) [10,48,160,260,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3254 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 82, targets := 1 }], pairs := [(0,5),(1,0),(4,0)], upper := (rows 11 50 164 268 84 33 66 193 321), lower := (rows 11 50 164 268 84 33 66 128 256), losses := [{ target := 5, region := (rows 3 2 4 28 16 0 67 227 355), good := (rows 459 475 396 268 476 449 451 128 256) }] }

theorem u3254 : Upper (D 6) (R 6) [10,48,160,260,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3255 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 132, targets := 65 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(2,6)], upper := (rows 11 50 164 328 21 96 65 134 262), lower := (rows 11 50 164 328 21 96 65 128 256), losses := [] }

theorem u3255 : Upper (D 6) (R 6) [10,48,160,320,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3256 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(2,1)], upper := (rows 11 50 164 328 21 96 66 133 261), lower := (rows 11 50 164 328 21 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 7 8 17 104 64 145 273), good := (rows 445 436 164 360 405 96 100 128 256) }] }

theorem u3256 : Upper (D 6) (R 6) [10,48,160,320,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3257 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 164 328 21 96 68 131 259), lower := (rows 11 50 164 328 21 96 68 128 256), losses := [] }

theorem u3257 : Upper (D 6) (R 6) [10,48,160,320,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3258 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 132, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 50 164 328 84 33 65 134 262), lower := (rows 11 50 164 328 84 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 38 72 16 32 64 131 259), good := (rows 398 438 164 328 92 420 456 128 256) }] }

theorem u3258 : Upper (D 6) (R 6) [10,48,160,320,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3259 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 164, targets := 66 },{ cop := 2, region := 82, targets := 1 }], pairs := [(1,0),(2,1),(2,6)], upper := (rows 11 50 164 328 84 33 66 133 261), lower := (rows 11 50 164 328 84 33 66 128 256), losses := [] }

theorem u3259 : Upper (D 6) (R 6) [10,48,160,320,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3260 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 299, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 164 328 84 33 68 131 259), lower := (rows 11 50 164 328 84 33 68 128 256), losses := [] }

theorem u3260 : Upper (D 6) (R 6) [10,48,160,320,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3261 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 196 13 273 96 66 164 292), lower := (rows 11 50 196 13 273 96 66 128 256), losses := [] }

theorem u3261 : Upper (D 6) (R 6) [10,48,192,5,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3262 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 7, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 196 13 273 96 68 162 290), lower := (rows 11 50 196 13 273 96 68 128 256), losses := [] }

theorem u3262 : Upper (D 6) (R 6) [10,48,192,5,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3263 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 196 13 273 96 96 134 262), lower := (rows 11 50 196 13 273 96 96 128 256), losses := [] }

theorem u3263 : Upper (D 6) (R 6) [10,48,192,5,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3264 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 13 274 36 65 224 352), lower := (rows 11 50 196 13 274 36 65 128 256), losses := [] }

theorem u3264 : Upper (D 6) (R 6) [10,48,192,5,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3265 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 7, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 50 196 13 274 36 96 193 321), lower := (rows 11 50 196 13 274 36 96 128 256), losses := [] }

theorem u3265 : Upper (D 6) (R 6) [10,48,192,5,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3266 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 13 274 96 65 164 292), lower := (rows 11 50 196 13 274 96 65 128 256), losses := [] }

theorem u3266 : Upper (D 6) (R 6) [10,48,192,5,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3267 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 7, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 50 196 13 274 96 68 161 289), lower := (rows 11 50 196 13 274 96 68 128 256), losses := [] }

theorem u3267 : Upper (D 6) (R 6) [10,48,192,5,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3268 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 114, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 196 13 274 96 96 133 261), lower := (rows 11 50 196 13 274 96 96 128 256), losses := [] }

theorem u3268 : Upper (D 6) (R 6) [10,48,192,5,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3269 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 13 276 96 65 162 290), lower := (rows 11 50 196 13 276 96 65 128 256), losses := [] }

theorem u3269 : Upper (D 6) (R 6) [10,48,192,5,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3270 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 98, targets := 5 }], pairs := [(1,0),(1,2),(4,1)], upper := (rows 11 50 196 13 276 96 66 161 289), lower := (rows 11 50 196 13 276 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 24 100 64 136 264), good := (rows 409 48 228 445 308 96 96 128 256) }] }

theorem u3270 : Upper (D 6) (R 6) [10,48,192,5,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3271 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 98, targets := 5 },{ cop := 7, region := 100, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 196 13 276 96 96 131 259), lower := (rows 11 50 196 13 276 96 96 128 256), losses := [] }

theorem u3271 : Upper (D 6) (R 6) [10,48,192,5,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3272 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 13 336 36 65 162 290), lower := (rows 11 50 196 13 336 36 65 128 256), losses := [] }

theorem u3272 : Upper (D 6) (R 6) [10,48,192,5,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3273 : Route 9 := (fun mask => (mask,id))

def c3273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3273 : Upper (D 6) (R 6) [10,48,192,5,320,4,2] 13 := by
  apply FastRouting.sound _ _ [10,48,192,5,320,4,2] 13 (by decide) (choices 1) [1,32] r3273 c3273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u234
  · exact u235

def b3274 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,2)], upper := (rows 11 50 196 13 336 36 96 131 259), lower := (rows 11 50 196 13 336 36 96 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 17 32 98 129 257), good := (rows 475 114 192 409 336 96 96 128 256) }] }

theorem u3274 : Upper (D 6) (R 6) [10,48,192,5,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3275 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 50 196 44 336 33 65 134 262), lower := (rows 11 50 196 44 336 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 16 97 97 128 256), good := (rows 105 112 236 108 368 97 97 128 256) }] }

theorem u3275 : Upper (D 6) (R 6) [10,48,192,36,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3276 : Route 9 := (fun mask => (mask,id))

def c3276 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3276 : Upper (D 6) (R 6) [10,48,192,36,320,1,2] 13 := by
  apply FastRouting.sound _ _ [10,48,192,36,320,1,2] 13 (by decide) (choices 1) [1,4] r3276 c3276
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u236
  · exact u237

def b3277 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 50 196 44 336 33 68 131 259), lower := (rows 11 50 196 44 336 33 68 128 256), losses := [] }

theorem u3277 : Upper (D 6) (R 6) [10,48,192,36,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3278 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 196 73 273 36 66 164 292), lower := (rows 11 50 196 73 273 36 66 128 256), losses := [] }

theorem u3278 : Upper (D 6) (R 6) [10,48,192,65,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3279 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 7, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 196 73 273 36 68 162 290), lower := (rows 11 50 196 73 273 36 68 128 256), losses := [] }

theorem u3279 : Upper (D 6) (R 6) [10,48,192,65,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3280 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 4, region := 230, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 196 73 273 36 96 134 262), lower := (rows 11 50 196 73 273 36 96 128 256), losses := [] }

theorem u3280 : Upper (D 6) (R 6) [10,48,192,65,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3281 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 196 73 274 36 65 164 292), lower := (rows 11 50 196 73 274 36 65 128 256), losses := [] }

theorem u3281 : Upper (D 6) (R 6) [10,48,192,65,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3282 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 7, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 50 196 73 274 36 68 161 289), lower := (rows 11 50 196 73 274 36 68 128 256), losses := [] }

theorem u3282 : Upper (D 6) (R 6) [10,48,192,65,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3283 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 1, region := 73, targets := 4 }], pairs := [(0,2),(2,1),(3,1)], upper := (rows 11 50 196 73 274 36 96 133 261), lower := (rows 11 50 196 73 274 36 96 128 256), losses := [] }

theorem u3283 : Upper (D 6) (R 6) [10,48,192,65,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3284 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 50 196 104 276 33 65 134 262), lower := (rows 11 50 196 104 276 33 65 128 256), losses := [] }

theorem u3284 : Upper (D 6) (R 6) [10,48,192,96,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3285 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 50 196 104 276 33 66 133 261), lower := (rows 11 50 196 104 276 33 66 128 256), losses := [] }

theorem u3285 : Upper (D 6) (R 6) [10,48,192,96,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3286 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 50 196 104 276 33 68 131 259), lower := (rows 11 50 196 104 276 33 68 128 256), losses := [] }

theorem u3286 : Upper (D 6) (R 6) [10,48,192,96,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3287 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 50 196 265 81 36 66 164 292), lower := (rows 11 50 196 265 81 36 66 128 256), losses := [] }

theorem u3287 : Upper (D 6) (R 6) [10,48,192,257,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3288 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 265, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 50 196 265 81 36 68 162 290), lower := (rows 11 50 196 265 81 36 68 128 256), losses := [] }

theorem u3288 : Upper (D 6) (R 6) [10,48,192,257,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3289 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 7, region := 100, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 196 265 81 36 96 134 262), lower := (rows 11 50 196 265 81 36 96 128 256), losses := [] }

theorem u3289 : Upper (D 6) (R 6) [10,48,192,257,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3290 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 11 50 196 268 21 96 65 162 290), lower := (rows 11 50 196 268 21 96 65 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 100 64 146 274), good := (rows 394 442 228 300 446 96 96 128 256) }] }

theorem u3290 : Upper (D 6) (R 6) [10,48,192,260,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3291 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 98, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,0),(1,2),(3,1)], upper := (rows 11 50 196 268 21 96 66 161 289), lower := (rows 11 50 196 268 21 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 100 64 144 272), good := (rows 9 440 228 300 445 96 96 128 256) }] }

theorem u3291 : Upper (D 6) (R 6) [10,48,192,260,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3292 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 100, targets := 3 },{ cop := 4, region := 98, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 196 268 21 96 96 131 259), lower := (rows 11 50 196 268 21 96 96 128 256), losses := [] }

theorem u3292 : Upper (D 6) (R 6) [10,48,192,260,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3293 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 50 196 268 81 36 65 162 290), lower := (rows 11 50 196 268 81 36 65 128 256), losses := [] }

theorem u3293 : Upper (D 6) (R 6) [10,48,192,260,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3294 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 4, region := 164, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 50 196 268 81 36 66 161 289), lower := (rows 11 50 196 268 81 36 66 128 256), losses := [] }

theorem u3294 : Upper (D 6) (R 6) [10,48,192,260,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3295 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 100, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 11 50 196 268 81 36 96 131 259), lower := (rows 11 50 196 268 81 36 96 128 256), losses := [{ target := 1, region := (rows 1 0 132 8 17 172 239 128 256), good := (rows 121 112 228 364 81 100 96 228 256) }] }

theorem u3295 : Upper (D 6) (R 6) [10,48,192,260,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3296 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 115, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 196 268 82 33 65 164 292), lower := (rows 11 50 196 268 82 33 65 128 256), losses := [] }

theorem u3296 : Upper (D 6) (R 6) [10,48,192,260,66,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3297 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 50 196 268 82 33 68 161 289), lower := (rows 11 50 196 268 82 33 68 128 256), losses := [] }

theorem u3297 : Upper (D 6) (R 6) [10,48,192,260,66,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3298 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 82, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 196 268 82 33 96 133 261), lower := (rows 11 50 196 268 82 33 96 128 256), losses := [] }

theorem u3298 : Upper (D 6) (R 6) [10,48,192,260,66,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3299 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 196 296 81 36 65 134 262), lower := (rows 11 50 196 296 81 36 65 128 256), losses := [] }

theorem u3299 : Upper (D 6) (R 6) [10,48,192,288,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3299
end Delivery.IrregularNine14.P06
