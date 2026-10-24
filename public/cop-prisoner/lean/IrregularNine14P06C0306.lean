import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0089

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18360 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 100 74 400 34 69 133 261), lower := (rows 25 35 100 74 400 34 64 128 256), losses := [] }

theorem u18360 : Upper (D 6) (R 6) [24,33,96,66,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18361 : Route 9 := (fun mask => (mask,id))

def c18361 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18361 : Upper (D 6) (R 6) [24,33,96,66,384,4] 13 := by
  apply FastRouting.sound _ _ [24,33,96,66,384,4] 13 (by decide) (choices 1) [1,2,4] r18361 c18361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5353
  · exact u5354
  · exact u5355

def b18362 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 100 137 274 34 68 196 324), lower := (rows 25 35 100 137 274 34 64 128 256), losses := [] }

theorem u18362 : Upper (D 6) (R 6) [24,33,96,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18363 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 340, targets := 1 },{ cop := 6, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 35 100 137 274 36 70 198 326), lower := (rows 25 35 100 137 274 36 64 128 256), losses := [] }

theorem u18363 : Upper (D 6) (R 6) [24,33,96,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18364 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 100 137 274 96 70 134 262), lower := (rows 25 35 100 137 274 96 64 128 256), losses := [] }

theorem u18364 : Upper (D 6) (R 6) [24,33,96,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18365 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 100 137 276 34 70 198 326), lower := (rows 25 35 100 137 276 34 64 128 256), losses := [] }

theorem u18365 : Upper (D 6) (R 6) [24,33,96,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18366 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 340, targets := 1 },{ cop := 1, region := 200, targets := 4 }], pairs := [(2,0),(3,2),(4,0)], upper := (rows 25 35 100 137 276 36 66 194 322), lower := (rows 25 35 100 137 276 36 64 128 256), losses := [] }

theorem u18366 : Upper (D 6) (R 6) [24,33,96,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18367 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 100 137 276 96 70 134 262), lower := (rows 25 35 100 137 276 96 64 128 256), losses := [] }

theorem u18367 : Upper (D 6) (R 6) [24,33,96,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18368 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 100 137 336 34 70 134 262), lower := (rows 25 35 100 137 336 34 64 128 256), losses := [] }

theorem u18368 : Upper (D 6) (R 6) [24,33,96,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18369 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 340, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 35 100 137 336 36 70 134 262), lower := (rows 25 35 100 137 336 36 64 128 256), losses := [] }

theorem u18369 : Upper (D 6) (R 6) [24,33,96,129,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18370 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 100 138 274 33 68 196 324), lower := (rows 25 35 100 138 274 33 64 128 256), losses := [] }

theorem u18370 : Upper (D 6) (R 6) [24,33,96,130,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18371 : Route 9 := (fun mask => (mask,id))

def c18371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18371 : Upper (D 6) (R 6) [24,33,96,130,258,4] 13 := by
  apply FastRouting.sound _ _ [24,33,96,130,258,4] 13 (by decide) (choices 1) [1,4] r18371 c18371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5356
  · exact u5357

def b18372 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 100 138 274 96 69 133 261), lower := (rows 25 35 100 138 274 96 64 128 256), losses := [] }

theorem u18372 : Upper (D 6) (R 6) [24,33,96,130,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18373 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 100 138 276 33 70 198 326), lower := (rows 25 35 100 138 276 33 64 128 256), losses := [] }

theorem u18373 : Upper (D 6) (R 6) [24,33,96,130,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18374 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 100 138 276 34 69 197 325), lower := (rows 25 35 100 138 276 34 64 128 256), losses := [] }

theorem u18374 : Upper (D 6) (R 6) [24,33,96,130,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18375 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 200, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(3,2),(3,5)], upper := (rows 25 35 100 138 276 36 67 195 323), lower := (rows 25 35 100 138 276 36 64 128 256), losses := [] }

theorem u18375 : Upper (D 6) (R 6) [24,33,96,130,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18376 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 100 138 276 96 71 135 263), lower := (rows 25 35 100 138 276 96 64 128 256), losses := [] }

theorem u18376 : Upper (D 6) (R 6) [24,33,96,130,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18377 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 100 138 336 33 70 134 262), lower := (rows 25 35 100 138 336 33 64 128 256), losses := [] }

theorem u18377 : Upper (D 6) (R 6) [24,33,96,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18378 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 100 138 336 34 69 133 261), lower := (rows 25 35 100 138 336 34 64 128 256), losses := [] }

theorem u18378 : Upper (D 6) (R 6) [24,33,96,130,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18379 : Route 9 := (fun mask => (mask,id))

def c18379 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18379 : Upper (D 6) (R 6) [24,33,96,130,320,4] 13 := by
  apply FastRouting.sound _ _ [24,33,96,130,320,4] 13 (by decide) (choices 1) [1,2,4] r18379 c18379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5358
  · exact u5359
  · exact u5360

def b18380 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 100 140 276 33 66 194 322), lower := (rows 25 35 100 140 276 33 64 128 256), losses := [] }

theorem u18380 : Upper (D 6) (R 6) [24,33,96,132,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18381 : Route 9 := (fun mask => (mask,id))

def c18381 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18381 : Upper (D 6) (R 6) [24,33,96,132,260,2] 13 := by
  apply FastRouting.sound _ _ [24,33,96,132,260,2] 13 (by decide) (choices 1) [1,2] r18381 c18381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5361
  · exact u5362

def b18382 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 100 140 276 96 67 131 259), lower := (rows 25 35 100 140 276 96 64 128 256), losses := [] }

theorem u18382 : Upper (D 6) (R 6) [24,33,96,132,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18383 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 25 35 100 140 336 33 70 134 262), lower := (rows 25 35 100 140 336 33 64 128 256), losses := [] }

theorem u18383 : Upper (D 6) (R 6) [24,33,96,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18384 : Route 9 := (fun mask => (mask,id))

def c18384 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18384 : Upper (D 6) (R 6) [24,33,96,132,320,2] 13 := by
  apply FastRouting.sound _ _ [24,33,96,132,320,2] 13 (by decide) (choices 1) [1,2,4] r18384 c18384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5363
  · exact u5364
  · exact u5365

def b18385 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 336, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 25 35 100 140 336 36 67 131 259), lower := (rows 25 35 100 140 336 36 64 128 256), losses := [] }

theorem u18385 : Upper (D 6) (R 6) [24,33,96,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18386 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(4,0),(4,2)], upper := (rows 25 35 133 14 82 36 352 480 352), lower := (rows 25 35 133 14 82 36 64 128 256), losses := [] }

theorem u18386 : Upper (D 6) (R 6) [24,33,129,6,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18387 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 396, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(2,1),(2,6),(3,6)], upper := (rows 25 35 133 14 82 96 356 420 292), lower := (rows 25 35 133 14 82 96 64 128 256), losses := [] }

theorem u18387 : Upper (D 6) (R 6) [24,33,129,6,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18388 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 484, targets := 2 },{ cop := 3, region := 368, targets := 1 }], pairs := [(2,1),(4,0)], upper := (rows 25 35 133 14 82 288 100 228 356), lower := (rows 25 35 133 14 82 288 64 128 256), losses := [] }

theorem u18388 : Upper (D 6) (R 6) [24,33,129,6,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18388 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18389 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 133 14 84 34 352 480 352), lower := (rows 25 35 133 14 84 34 64 128 256), losses := [] }

theorem u18389 : Upper (D 6) (R 6) [24,33,129,6,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18390 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 396, targets := 64 },{ cop := 0, region := 354, targets := 4 }], pairs := [(1,2),(2,6),(3,6)], upper := (rows 25 35 133 14 84 96 354 418 290), lower := (rows 25 35 133 14 84 96 64 128 256), losses := [] }

theorem u18390 : Upper (D 6) (R 6) [24,33,129,6,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18391 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 354, targets := 4 },{ cop := 3, region := 368, targets := 1 }], pairs := [(1,2),(4,0)], upper := (rows 25 35 133 14 84 288 98 226 354), lower := (rows 25 35 133 14 84 288 64 128 256), losses := [] }

theorem u18391 : Upper (D 6) (R 6) [24,33,129,6,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18391 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18392 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(4,0),(4,2)], upper := (rows 25 35 133 14 274 36 96 224 352), lower := (rows 25 35 133 14 274 36 64 128 256), losses := [] }

theorem u18392 : Upper (D 6) (R 6) [24,33,129,6,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18393 : Route 9 := (fun mask => (mask,id))

def c18393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18393 : Upper (D 6) (R 6) [24,33,129,6,258,64] 13 := by
  apply FastRouting.sound _ _ [24,33,129,6,258,64] 13 (by decide) (choices 1) [4,32] r18393 c18393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5366
  · exact u5367

def b18394 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 35 133 14 276 34 96 224 352), lower := (rows 25 35 133 14 276 34 64 128 256), losses := [] }

theorem u18394 : Upper (D 6) (R 6) [24,33,129,6,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18395 : Route 9 := (fun mask => (mask,id))

def c18395 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18395 : Upper (D 6) (R 6) [24,33,129,6,260,64] 13 := by
  apply FastRouting.sound _ _ [24,33,129,6,260,64] 13 (by decide) (choices 1) [2,32] r18395 c18395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5368
  · exact u5369

def b18396 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 133 14 336 34 100 228 356), lower := (rows 25 35 133 14 336 34 64 128 256), losses := [] }

theorem u18396 : Upper (D 6) (R 6) [24,33,129,6,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18397 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 336, targets := 5 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(4,0),(4,2)], upper := (rows 25 35 133 14 336 36 98 226 354), lower := (rows 25 35 133 14 336 36 64 128 256), losses := [] }

theorem u18397 : Upper (D 6) (R 6) [24,33,129,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18398 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 140, targets := 64 },{ cop := 3, region := 368, targets := 1 }], pairs := [(2,6),(3,6),(4,0)], upper := (rows 25 35 133 14 336 96 102 166 294), lower := (rows 25 35 133 14 336 96 64 128 256), losses := [] }

theorem u18398 : Upper (D 6) (R 6) [24,33,129,6,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18399 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 133 44 82 34 324 452 324), lower := (rows 25 35 133 44 82 34 64 128 256), losses := [] }

theorem u18399 : Upper (D 6) (R 6) [24,33,129,36,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18400 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 25 35 133 44 82 36 322 450 322), lower := (rows 25 35 133 44 82 36 64 128 256), losses := [] }

theorem u18400 : Upper (D 6) (R 6) [24,33,129,36,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18401 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 388, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 25 35 133 44 82 96 326 390 262), lower := (rows 25 35 133 44 82 96 64 128 256), losses := [] }

theorem u18401 : Upper (D 6) (R 6) [24,33,129,36,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18402 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 25 35 133 44 82 288 70 198 326), lower := (rows 25 35 133 44 82 288 64 128 256), losses := [] }

theorem u18402 : Upper (D 6) (R 6) [24,33,129,36,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18402 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18403 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 133 44 274 34 68 196 324), lower := (rows 25 35 133 44 274 34 64 128 256), losses := [] }

theorem u18403 : Upper (D 6) (R 6) [24,33,129,36,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18404 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 25 35 133 44 274 36 66 194 322), lower := (rows 25 35 133 44 274 36 64 128 256), losses := [] }

theorem u18404 : Upper (D 6) (R 6) [24,33,129,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18405 : Route 9 := (fun mask => (mask,id))

def c18405 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18405 : Upper (D 6) (R 6) [24,33,129,36,258,64] 13 := by
  apply FastRouting.sound _ _ [24,33,129,36,258,64] 13 (by decide) (choices 1) [2,4] r18405 c18405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5370
  · exact u5371

def b18406 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 32 }], pairs := [(1,2),(1,6),(2,5)], upper := (rows 25 35 133 44 336 34 70 198 326), lower := (rows 25 35 133 44 336 34 64 128 256), losses := [] }

theorem u18406 : Upper (D 6) (R 6) [24,33,129,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18406 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18407 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 339, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 25 35 133 44 336 36 66 194 322), lower := (rows 25 35 133 44 336 36 64 128 256), losses := [] }

theorem u18407 : Upper (D 6) (R 6) [24,33,129,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18408 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 25 35 133 44 336 96 70 134 262), lower := (rows 25 35 133 44 336 96 64 128 256), losses := [] }

theorem u18408 : Upper (D 6) (R 6) [24,33,129,36,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18409 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 35 133 74 84 34 356 420 292), lower := (rows 25 35 133 74 84 34 64 128 256), losses := [] }

theorem u18409 : Upper (D 6) (R 6) [24,33,129,66,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18410 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 422, targets := 64 },{ cop := 1, region := 328, targets := 1 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 25 35 133 74 84 36 354 418 290), lower := (rows 25 35 133 74 84 36 64 128 256), losses := [] }

theorem u18410 : Upper (D 6) (R 6) [24,33,129,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18411 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 25 35 133 74 84 288 102 166 294), lower := (rows 25 35 133 74 84 288 64 128 256), losses := [] }

theorem u18411 : Upper (D 6) (R 6) [24,33,129,66,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18411 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18412 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,1),(3,0)], upper := (rows 25 35 133 74 274 36 100 228 356), lower := (rows 25 35 133 74 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 18 36 100 164 292), good := (rows 24 506 484 90 282 484 64 128 256) }] }

theorem u18412 : Upper (D 6) (R 6) [24,33,129,66,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18413 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 404, targets := 64 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(2,6),(4,6)], upper := (rows 25 35 133 74 274 96 100 164 292), lower := (rows 25 35 133 74 274 96 64 128 256), losses := [] }

theorem u18413 : Upper (D 6) (R 6) [24,33,129,66,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18414 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 196, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 133 74 276 34 100 228 356), lower := (rows 25 35 133 74 276 34 64 128 256), losses := [] }

theorem u18414 : Upper (D 6) (R 6) [24,33,129,66,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18415 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 72, targets := 5 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,2)], upper := (rows 25 35 133 74 276 36 98 226 354), lower := (rows 25 35 133 74 276 36 64 128 256), losses := [] }

theorem u18415 : Upper (D 6) (R 6) [24,33,129,66,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18416 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 404, targets := 64 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 25 35 133 74 276 96 102 166 294), lower := (rows 25 35 133 74 276 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 104 64 128 256), good := (rows 59 35 131 106 272 96 96 128 256) }] }

theorem u18416 : Upper (D 6) (R 6) [24,33,129,66,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18417 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 0, region := 34, targets := 4 }], pairs := [(1,2),(2,1),(2,5)], upper := (rows 25 35 133 74 304 34 68 196 324), lower := (rows 25 35 133 74 304 34 64 128 256), losses := [] }

theorem u18417 : Upper (D 6) (R 6) [24,33,129,66,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18418 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,5),(3,5)], upper := (rows 25 35 133 74 304 36 70 198 326), lower := (rows 25 35 133 74 304 36 64 128 256), losses := [] }

theorem u18418 : Upper (D 6) (R 6) [24,33,129,66,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18419 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 1, region := 132, targets := 64 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 25 35 133 74 304 96 70 134 262), lower := (rows 25 35 133 74 304 96 64 128 256), losses := [] }

theorem u18419 : Upper (D 6) (R 6) [24,33,129,66,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u18419
end Delivery.IrregularNine14.P06
