import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0221
import IrregularNine14P06C0222

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31260 : PairBound 9 := { available := 291, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 84 137 84 291 355 419 291), lower := (rows 11 38 84 137 84 32 64 128 256), losses := [] }

theorem u31260 : Upper (D 6) (R 6) [10,36,80,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31261 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 137 112 295 327 391 263), lower := (rows 11 38 84 137 112 32 64 128 256), losses := [] }

theorem u31261 : Upper (D 6) (R 6) [10,36,80,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31262 : Route 9 := (fun mask => (mask,id))

def c31262 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31262 : Upper (D 6) (R 6) [10,36,80,129,257] 13 := by
  apply FastRouting.sound _ _ [10,36,80,129,257] 13 (by decide) (choices 1) [2,4,64] r31262 c31262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13307
  · exact u13308
  · exact u13309

def r31263 : Route 9 := (fun mask => (mask,id))

def c31263 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31263 : Upper (D 6) (R 6) [10,36,80,129,258] 13 := by
  apply FastRouting.sound _ _ [10,36,80,129,258] 13 (by decide) (choices 1) [1,4,64] r31263 c31263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13310
  · exact u13311
  · exact u13312

def r31264 : Route 9 := (fun mask => (mask,id))

def c31264 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31264 : Upper (D 6) (R 6) [10,36,80,129,260] 13 := by
  apply FastRouting.sound _ _ [10,36,80,129,260] 13 (by decide) (choices 1) [1,2,64] r31264 c31264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13313
  · exact u13314
  · exact u13315

def r31265 : Route 9 := (fun mask => (mask,id))

def c31265 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31265 : Upper (D 6) (R 6) [10,36,80,129,288] 13 := by
  apply FastRouting.sound _ _ [10,36,80,129,288] 13 (by decide) (choices 1) [1,2,4,64] r31265 c31265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13316
  · exact u13317
  · exact u13318
  · exact u13319

def b31266 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 137 336 39 103 167 295), lower := (rows 11 38 84 137 336 32 64 128 256), losses := [] }

theorem u31266 : Upper (D 6) (R 6) [10,36,80,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31267 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 38 84 140 19 353 353 481 353), lower := (rows 11 38 84 140 19 32 64 128 256), losses := [] }

theorem u31267 : Upper (D 6) (R 6) [10,36,80,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31268 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 457, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 38 84 140 49 355 323 451 323), lower := (rows 11 38 84 140 49 32 64 128 256), losses := [] }

theorem u31268 : Upper (D 6) (R 6) [10,36,80,132,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31269 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 84 140 50 353 321 449 321), lower := (rows 11 38 84 140 50 32 64 128 256), losses := [] }

theorem u31269 : Upper (D 6) (R 6) [10,36,80,132,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31270 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 140 81 291 355 419 291), lower := (rows 11 38 84 140 81 32 64 128 256), losses := [] }

theorem u31270 : Upper (D 6) (R 6) [10,36,80,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31271 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 140 82 289 353 417 289), lower := (rows 11 38 84 140 82 32 64 128 256), losses := [] }

theorem u31271 : Upper (D 6) (R 6) [10,36,80,132,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31272 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 140 112 291 323 387 259), lower := (rows 11 38 84 140 112 32 64 128 256), losses := [] }

theorem u31272 : Upper (D 6) (R 6) [10,36,80,132,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31273 : Route 9 := (fun mask => (mask,id))

def c31273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31273 : Upper (D 6) (R 6) [10,36,80,132,257] 13 := by
  apply FastRouting.sound _ _ [10,36,80,132,257] 13 (by decide) (choices 1) [1,2,64] r31273 c31273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13320
  · exact u13321
  · exact u13322

def r31274 : Route 9 := (fun mask => (mask,id))

def c31274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31274 : Upper (D 6) (R 6) [10,36,80,132,258] 13 := by
  apply FastRouting.sound _ _ [10,36,80,132,258] 13 (by decide) (choices 1) [1,64] r31274 c31274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13323
  · exact u13324

def b31275 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 201, targets := 32 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,5),(3,5),(4,2)], upper := (rows 11 38 84 140 304 99 67 195 323), lower := (rows 11 38 84 140 304 32 64 128 256), losses := [] }

theorem u31275 : Upper (D 6) (R 6) [10,36,80,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31276 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 140 336 35 99 163 291), lower := (rows 11 38 84 140 336 32 64 128 256), losses := [] }

theorem u31276 : Upper (D 6) (R 6) [10,36,80,132,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31277 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 38 84 168 19 357 325 453 325), lower := (rows 11 38 84 168 19 32 64 128 256), losses := [] }

theorem u31277 : Upper (D 6) (R 6) [10,36,80,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31278 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 457, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 84 168 21 355 323 451 323), lower := (rows 11 38 84 168 21 32 64 128 256), losses := [] }

theorem u31278 : Upper (D 6) (R 6) [10,36,80,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31279 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 84 168 22 353 321 449 321), lower := (rows 11 38 84 168 22 32 64 128 256), losses := [] }

theorem u31279 : Upper (D 6) (R 6) [10,36,80,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31280 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 168 81 295 327 391 263), lower := (rows 11 38 84 168 81 32 64 128 256), losses := [] }

theorem u31280 : Upper (D 6) (R 6) [10,36,80,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31281 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 168 82 293 325 389 261), lower := (rows 11 38 84 168 82 32 64 128 256), losses := [] }

theorem u31281 : Upper (D 6) (R 6) [10,36,80,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31282 : PairBound 9 := { available := 259, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 84 168 84 291 323 387 259), lower := (rows 11 38 84 168 84 32 64 128 256), losses := [] }

theorem u31282 : Upper (D 6) (R 6) [10,36,80,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31283 : Route 9 := (fun mask => (mask,id))

def c31283 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31283 : Upper (D 6) (R 6) [10,36,80,160,257] 13 := by
  apply FastRouting.sound _ _ [10,36,80,160,257] 13 (by decide) (choices 1) [1,2,4,64] r31283 c31283
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13325
  · exact u13326
  · exact u13327
  · exact u13328

def r31284 : Route 9 := (fun mask => (mask,id))

def c31284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31284 : Upper (D 6) (R 6) [10,36,80,160,258] 13 := by
  apply FastRouting.sound _ _ [10,36,80,160,258] 13 (by decide) (choices 1) [1,4,64] r31284 c31284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13329
  · exact u13330
  · exact u13331

def b31285 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 1, region := 201, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 84 168 276 99 67 195 323), lower := (rows 11 38 84 168 276 32 64 128 256), losses := [] }

theorem u31285 : Upper (D 6) (R 6) [10,36,80,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31286 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 168 336 39 71 135 263), lower := (rows 11 38 84 168 336 32 64 128 256), losses := [] }

theorem u31286 : Upper (D 6) (R 6) [10,36,80,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31287 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 84 200 19 293 357 421 293), lower := (rows 11 38 84 200 19 32 64 128 256), losses := [] }

theorem u31287 : Upper (D 6) (R 6) [10,36,80,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31288 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 457, targets := 4 },{ cop := 4, region := 290, targets := 64 }], pairs := [(0,2),(1,6),(3,2)], upper := (rows 11 38 84 200 21 291 355 419 291), lower := (rows 11 38 84 200 21 32 64 128 256), losses := [] }

theorem u31288 : Upper (D 6) (R 6) [10,36,80,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31289 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 84 200 22 289 353 417 289), lower := (rows 11 38 84 200 22 32 64 128 256), losses := [] }

theorem u31289 : Upper (D 6) (R 6) [10,36,80,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31290 : Route 9 := (fun mask => (mask,id))

def c31290 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31290 : Upper (D 6) (R 6) [10,36,80,192,33] 13 := by
  apply FastRouting.sound _ _ [10,36,80,192,33] 13 (by decide) (choices 1) [1,2,4,256] r31290 c31290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13332
  · exact u13333
  · exact u13334
  · exact u13335

def b31291 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 84 200 50 293 325 389 261), lower := (rows 11 38 84 200 50 32 64 128 256), losses := [] }

theorem u31291 : Upper (D 6) (R 6) [10,36,80,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31292 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 1, region := 457, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 38 84 200 52 291 323 387 259), lower := (rows 11 38 84 200 52 32 64 128 256), losses := [] }

theorem u31292 : Upper (D 6) (R 6) [10,36,80,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31293 : Route 9 := (fun mask => (mask,id))

def c31293 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31293 : Upper (D 6) (R 6) [10,36,80,192,257] 13 := by
  apply FastRouting.sound _ _ [10,36,80,192,257] 13 (by decide) (choices 1) [1,2,4] r31293 c31293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13336
  · exact u13337
  · exact u13338

def r31294 : Route 9 := (fun mask => (mask,id))

def c31294 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31294 : Upper (D 6) (R 6) [10,36,80,192,258] 13 := by
  apply FastRouting.sound _ _ [10,36,80,192,258] 13 (by decide) (choices 1) [1,4] r31294 c31294
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13339
  · exact u13340

def r31295 : Route 9 := (fun mask => (mask,id))

def c31295 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31295 : Upper (D 6) (R 6) [10,36,80,192,260] 13 := by
  apply FastRouting.sound _ _ [10,36,80,192,260] 13 (by decide) (choices 1) [1,2] r31295 c31295
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13341
  · exact u13342

def r31296 : Route 9 := (fun mask => (mask,id))

def c31296 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31296 : Upper (D 6) (R 6) [10,36,80,192,288] 13 := by
  apply FastRouting.sound _ _ [10,36,80,192,288] 13 (by decide) (choices 1) [1,2,4] r31296 c31296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13343
  · exact u13344
  · exact u13345

def b31297 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 84 392 19 101 101 229 357), lower := (rows 11 38 84 392 19 32 64 128 256), losses := [] }

theorem u31297 : Upper (D 6) (R 6) [10,36,80,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31298 : Route 9 := (fun mask => (mask,id))

def c31298 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31298 : Upper (D 6) (R 6) [10,36,80,384,5] 13 := by
  apply FastRouting.sound _ _ [10,36,80,384,5] 13 (by decide) (choices 1) [1,2,64] r31298 c31298
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13346
  · exact u13347
  · exact u13348

def b31299 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 84 392 22 97 97 225 353), lower := (rows 11 38 84 392 22 32 64 128 256), losses := [] }

theorem u31299 : Upper (D 6) (R 6) [10,36,80,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31300 : Route 9 := (fun mask => (mask,id))

def c31300 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31300 : Upper (D 6) (R 6) [10,36,80,384,33] 13 := by
  apply FastRouting.sound _ _ [10,36,80,384,33] 13 (by decide) (choices 1) [1,2,4,64] r31300 c31300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13349
  · exact u13350
  · exact u13351
  · exact u13352

def b31301 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 84 392 50 101 69 197 325), lower := (rows 11 38 84 392 50 32 64 128 256), losses := [] }

theorem u31301 : Upper (D 6) (R 6) [10,36,80,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31301 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31302 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 1, region := 457, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 38 84 392 52 99 67 195 323), lower := (rows 11 38 84 392 52 32 64 128 256), losses := [] }

theorem u31302 : Upper (D 6) (R 6) [10,36,80,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31303 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 392 81 39 103 167 295), lower := (rows 11 38 84 392 81 32 64 128 256), losses := [] }

theorem u31303 : Upper (D 6) (R 6) [10,36,80,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31303 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31304 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 392 82 37 101 165 293), lower := (rows 11 38 84 392 82 32 64 128 256), losses := [] }

theorem u31304 : Upper (D 6) (R 6) [10,36,80,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31304 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31305 : PairBound 9 := { available := 35, camps := [{ cop := 6, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 38 84 392 84 35 99 163 291), lower := (rows 11 38 84 392 84 32 64 128 256), losses := [] }

theorem u31305 : Upper (D 6) (R 6) [10,36,80,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31306 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 84 392 112 39 71 135 263), lower := (rows 11 38 84 392 112 32 64 128 256), losses := [] }

theorem u31306 : Upper (D 6) (R 6) [10,36,80,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31306 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31307 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 133 25 22 352 352 480 352), lower := (rows 11 38 133 25 22 32 64 128 256), losses := [] }

theorem u31307 : Upper (D 6) (R 6) [10,36,129,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31307 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31308 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 133 25 50 356 324 452 324), lower := (rows 11 38 133 25 50 32 64 128 256), losses := [] }

theorem u31308 : Upper (D 6) (R 6) [10,36,129,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31308 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31309 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 133 25 52 354 322 450 322), lower := (rows 11 38 133 25 52 32 64 128 256), losses := [] }

theorem u31309 : Upper (D 6) (R 6) [10,36,129,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31309 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31310 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 133 25 82 356 356 484 356), lower := (rows 11 38 133 25 82 32 64 128 256), losses := [] }

theorem u31310 : Upper (D 6) (R 6) [10,36,129,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31310 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31311 : Route 9 := (fun mask => (mask,id))

def c31311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31311 : Upper (D 6) (R 6) [10,36,129,17,68] 13 := by
  apply FastRouting.sound _ _ [10,36,129,17,68] 13 (by decide) (choices 1) [2,64,256] r31311 c31311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13353
  · exact u13354
  · exact u13355

def b31312 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 0, region := 452, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 38 133 25 112 358 326 454 326), lower := (rows 11 38 133 25 112 32 64 128 256), losses := [] }

theorem u31312 : Upper (D 6) (R 6) [10,36,129,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31313 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 133 25 274 100 100 228 356), lower := (rows 11 38 133 25 274 32 64 128 256), losses := [] }

theorem u31313 : Upper (D 6) (R 6) [10,36,129,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31313 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31314 : Route 9 := (fun mask => (mask,id))

def c31314 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31314 : Upper (D 6) (R 6) [10,36,129,17,260] 13 := by
  apply FastRouting.sound _ _ [10,36,129,17,260] 13 (by decide) (choices 1) [2,64] r31314 c31314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13356
  · exact u13357

def b31315 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 0, region := 196, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 11 38 133 25 304 102 70 198 326), lower := (rows 11 38 133 25 304 32 64 128 256), losses := [] }

theorem u31315 : Upper (D 6) (R 6) [10,36,129,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31316 : Route 9 := (fun mask => (mask,id))

def c31316 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31316 : Upper (D 6) (R 6) [10,36,129,17,320] 13 := by
  apply FastRouting.sound _ _ [10,36,129,17,320] 13 (by decide) (choices 1) [2,4,64] r31316 c31316
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13358
  · exact u13359
  · exact u13360

def b31317 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 133 28 19 352 352 480 352), lower := (rows 11 38 133 28 19 32 64 128 256), losses := [] }

theorem u31317 : Upper (D 6) (R 6) [10,36,129,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31317 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31318 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 133 28 49 354 322 450 322), lower := (rows 11 38 133 28 49 32 64 128 256), losses := [] }

theorem u31318 : Upper (D 6) (R 6) [10,36,129,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31319 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 133 28 50 353 321 449 321), lower := (rows 11 38 133 28 50 32 64 128 256), losses := [] }

theorem u31319 : Upper (D 6) (R 6) [10,36,129,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u31319
end Delivery.IrregularNine14.P06
