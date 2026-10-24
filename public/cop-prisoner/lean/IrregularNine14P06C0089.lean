import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0006

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5340 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 1, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 70 140 336 34 68 161 289), lower := (rows 25 35 70 140 336 34 68 128 256), losses := [] }

theorem u5340 : Upper (D 6) (R 6) [24,33,66,132,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5340 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5341 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 70 140 336 34 96 133 261), lower := (rows 25 35 70 140 336 34 96 128 256), losses := [] }

theorem u5341 : Upper (D 6) (R 6) [24,33,66,132,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5342 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 340, targets := 32 },{ cop := 2, region := 168, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 25 35 70 168 336 36 65 134 262), lower := (rows 25 35 70 168 336 36 65 128 256), losses := [] }

theorem u5342 : Upper (D 6) (R 6) [24,33,66,160,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5343 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 441, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 35 70 168 336 36 66 133 261), lower := (rows 25 35 70 168 336 36 66 128 256), losses := [] }

theorem u5343 : Upper (D 6) (R 6) [24,33,66,160,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5344 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 136, targets := 68 },{ cop := 1, region := 68, targets := 32 }], pairs := [(2,5),(3,2),(3,6)], upper := (rows 25 35 70 168 336 36 68 131 259), lower := (rows 25 35 70 168 336 36 68 128 256), losses := [] }

theorem u5344 : Upper (D 6) (R 6) [24,33,66,160,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5345 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 25 35 100 74 146 36 65 388 260), lower := (rows 25 35 100 74 146 36 65 128 256), losses := [] }

theorem u5345 : Upper (D 6) (R 6) [24,33,96,66,130,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5346 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 401, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 35 100 74 146 36 68 385 257), lower := (rows 25 35 100 74 146 36 68 128 256), losses := [] }

theorem u5346 : Upper (D 6) (R 6) [24,33,96,66,130,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5347 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 25 35 100 74 146 36 320 133 261), lower := (rows 25 35 100 74 146 36 320 128 256), losses := [] }

theorem u5347 : Upper (D 6) (R 6) [24,33,96,66,130,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5347 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5348 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 25 35 100 74 146 288 65 132 260), lower := (rows 25 35 100 74 146 288 65 128 256), losses := [] }

theorem u5348 : Upper (D 6) (R 6) [24,33,96,66,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5348 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5349 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 25 35 100 74 146 288 68 133 261), lower := (rows 25 35 100 74 146 288 68 128 256), losses := [] }

theorem u5349 : Upper (D 6) (R 6) [24,33,96,66,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5349 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5350 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 25 35 100 74 148 288 65 134 262), lower := (rows 25 35 100 74 148 288 65 128 256), losses := [] }

theorem u5350 : Upper (D 6) (R 6) [24,33,96,66,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5350 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5351 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 437, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 25 35 100 74 148 288 66 133 261), lower := (rows 25 35 100 74 148 288 66 128 256), losses := [] }

theorem u5351 : Upper (D 6) (R 6) [24,33,96,66,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5351 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5352 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 290, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 25 35 100 74 148 288 68 131 259), lower := (rows 25 35 100 74 148 288 68 128 256), losses := [] }

theorem u5352 : Upper (D 6) (R 6) [24,33,96,66,132,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5352 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5353 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 72, targets := 36 },{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0),(3,2),(3,5)], upper := (rows 25 35 100 74 400 36 65 134 262), lower := (rows 25 35 100 74 400 36 65 128 256), losses := [] }

theorem u5353 : Upper (D 6) (R 6) [24,33,96,66,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5354 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 437, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 25 35 100 74 400 36 66 133 261), lower := (rows 25 35 100 74 400 36 66 128 256), losses := [] }

theorem u5354 : Upper (D 6) (R 6) [24,33,96,66,384,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5354 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5355 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 401, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 25 35 100 74 400 36 68 131 259), lower := (rows 25 35 100 74 400 36 68 128 256), losses := [] }

theorem u5355 : Upper (D 6) (R 6) [24,33,96,66,384,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5355 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5356 : Route 9 := (fun mask => (mask,id))

def c5356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5356 : Upper (D 6) (R 6) [24,33,96,130,258,4,1] 13 := by
  apply FastRouting.sound _ _ [24,33,96,130,258,4,1] 13 (by decide) (choices 1) [4,64] r5356 c5356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u389
  · exact u390

def b5357 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 35 100 138 274 36 68 193 321), lower := (rows 25 35 100 138 274 36 68 128 256), losses := [] }

theorem u5357 : Upper (D 6) (R 6) [24,33,96,130,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5357 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5358 : Route 9 := (fun mask => (mask,id))

def c5358 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5358 : Upper (D 6) (R 6) [24,33,96,130,320,4,1] 13 := by
  apply FastRouting.sound _ _ [24,33,96,130,320,4,1] 13 (by decide) (choices 1) [2,4] r5358 c5358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u391
  · exact u392

def r5359 : Route 9 := (fun mask => (mask,id))

def c5359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5359 : Upper (D 6) (R 6) [24,33,96,130,320,4,2] 13 := by
  apply FastRouting.sound _ _ [24,33,96,130,320,4,2] 13 (by decide) (choices 1) [1,4] r5359 c5359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u393
  · exact u394

def b5360 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 35 100 138 336 36 68 131 259), lower := (rows 25 35 100 138 336 36 68 128 256), losses := [] }

theorem u5360 : Upper (D 6) (R 6) [24,33,96,130,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5361 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 34, targets := 4 },{ cop := 0, region := 34, targets := 64 },{ cop := 1, region := 68, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 100 140 276 34 65 194 322), lower := (rows 25 35 100 140 276 34 65 128 256), losses := [] }

theorem u5361 : Upper (D 6) (R 6) [24,33,96,132,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5362 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 409, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 100 140 276 34 66 193 321), lower := (rows 25 35 100 140 276 34 66 128 256), losses := [] }

theorem u5362 : Upper (D 6) (R 6) [24,33,96,132,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5363 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 34, targets := 4 },{ cop := 0, region := 34, targets := 64 },{ cop := 1, region := 68, targets := 2 }], pairs := [(1,2),(1,6),(2,1)], upper := (rows 25 35 100 140 336 34 65 134 262), lower := (rows 25 35 100 140 336 34 65 128 256), losses := [] }

theorem u5363 : Upper (D 6) (R 6) [24,33,96,132,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5364 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 409, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 100 140 336 34 66 133 261), lower := (rows 25 35 100 140 336 34 66 128 256), losses := [] }

theorem u5364 : Upper (D 6) (R 6) [24,33,96,132,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5365 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 34, targets := 68 },{ cop := 5, region := 68, targets := 1 }], pairs := [(1,2),(1,6),(2,0)], upper := (rows 25 35 100 140 336 34 68 131 259), lower := (rows 25 35 100 140 336 34 68 128 256), losses := [] }

theorem u5365 : Upper (D 6) (R 6) [24,33,96,132,320,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5366 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 3, region := 368, targets := 1 }], pairs := [(0,2),(2,1),(4,0)], upper := (rows 25 35 133 14 274 96 68 224 352), lower := (rows 25 35 133 14 274 96 68 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 18 96 64 224 352), good := (rows 25 435 129 27 274 480 480 128 256) }] }

theorem u5366 : Upper (D 6) (R 6) [24,33,129,6,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5367 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 98, targets := 4 },{ cop := 3, region := 368, targets := 1 }], pairs := [(1,2),(2,1),(4,0)], upper := (rows 25 35 133 14 274 96 96 196 324), lower := (rows 25 35 133 14 274 96 96 128 256), losses := [] }

theorem u5367 : Upper (D 6) (R 6) [24,33,129,6,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5368 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 98, targets := 4 },{ cop := 3, region := 368, targets := 1 }], pairs := [(0,1),(1,2),(4,0)], upper := (rows 25 35 133 14 276 96 66 224 352), lower := (rows 25 35 133 14 276 96 66 128 256), losses := [{ target := 1, region := (rows 9 0 6 8 82 96 64 224 352), good := (rows 25 437 133 29 276 496 500 128 256) }] }

theorem u5368 : Upper (D 6) (R 6) [24,33,129,6,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5369 : Route 9 := (fun mask => (mask,id))

def c5369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5369 : Upper (D 6) (R 6) [24,33,129,6,260,64,32] 13 := by
  apply FastRouting.sound _ _ [24,33,129,6,260,64,32] 13 (by decide) (choices 1) [2,64] r5369 c5369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u395
  · exact u396

def b5370 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 25 35 133 44 274 96 66 196 324), lower := (rows 25 35 133 44 274 96 66 128 256), losses := [] }

theorem u5370 : Upper (D 6) (R 6) [24,33,129,36,258,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5371 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 2, region := 104, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 25 35 133 44 274 96 68 194 322), lower := (rows 25 35 133 44 274 96 68 128 256), losses := [] }

theorem u5371 : Upper (D 6) (R 6) [24,33,129,36,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5372 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 72, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 25 35 133 74 336 36 66 164 292), lower := (rows 25 35 133 74 336 36 66 128 256), losses := [] }

theorem u5372 : Upper (D 6) (R 6) [24,33,129,66,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5373 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 25 35 133 74 336 36 68 162 290), lower := (rows 25 35 133 74 336 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 26 100 100 138 266), good := (rows 408 506 228 506 368 100 100 128 256) }] }

theorem u5373 : Upper (D 6) (R 6) [24,33,129,66,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5374 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 133 74 336 36 96 134 262), lower := (rows 25 35 133 74 336 36 96 128 256), losses := [] }

theorem u5374 : Upper (D 6) (R 6) [24,33,129,66,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5375 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 34, targets := 4 },{ cop := 0, region := 34, targets := 64 }], pairs := [(1,2),(1,6),(4,0)], upper := (rows 25 35 133 76 276 34 66 224 352), lower := (rows 25 35 133 76 276 34 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 98 98 234 362), good := (rows 408 482 132 508 276 482 482 128 256) }] }

theorem u5375 : Upper (D 6) (R 6) [24,33,129,68,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5376 : Route 9 := (fun mask => (mask,id))

def c5376 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5376 : Upper (D 6) (R 6) [24,33,129,68,260,2,32] 13 := by
  apply FastRouting.sound _ _ [24,33,129,68,260,2,32] 13 (by decide) (choices 1) [2,64] r5376 c5376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u397
  · exact u398

def b5377 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0),(4,2)], upper := (rows 25 35 134 13 274 96 68 224 352), lower := (rows 25 35 134 13 274 96 68 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 18 96 64 224 352), good := (rows 25 435 146 9 274 480 480 128 256) }] }

theorem u5377 : Upper (D 6) (R 6) [24,33,130,5,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5378 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 25 35 134 13 274 96 96 196 324), lower := (rows 25 35 134 13 274 96 96 128 256), losses := [] }

theorem u5378 : Upper (D 6) (R 6) [24,33,130,5,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5379 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 35 134 74 304 36 65 196 324), lower := (rows 25 35 134 74 304 36 65 128 256), losses := [] }

theorem u5379 : Upper (D 6) (R 6) [24,33,130,66,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5380 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 2, region := 72, targets := 1 }], pairs := [(2,5),(3,0),(3,5)], upper := (rows 25 35 134 74 304 36 68 193 321), lower := (rows 25 35 134 74 304 36 68 128 256), losses := [] }

theorem u5380 : Upper (D 6) (R 6) [24,33,130,66,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5381 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 1, region := 72, targets := 4 }], pairs := [(1,6),(2,6),(3,2)], upper := (rows 25 35 134 74 336 36 65 164 292), lower := (rows 25 35 134 74 336 36 65 128 256), losses := [] }

theorem u5381 : Upper (D 6) (R 6) [24,33,130,66,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5382 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 2, region := 72, targets := 1 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 25 35 134 74 336 36 68 161 289), lower := (rows 25 35 134 74 336 36 68 128 256), losses := [] }

theorem u5382 : Upper (D 6) (R 6) [24,33,130,66,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5383 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 35 134 74 336 36 96 133 261), lower := (rows 25 35 134 74 336 36 96 128 256), losses := [] }

theorem u5383 : Upper (D 6) (R 6) [24,33,130,66,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5384 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 468, targets := 32 },{ cop := 1, region := 72, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 25 35 134 104 274 36 65 196 324), lower := (rows 25 35 134 104 274 36 65 128 256), losses := [] }

theorem u5384 : Upper (D 6) (R 6) [24,33,130,96,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5385 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 275, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 25 35 134 104 274 36 68 193 321), lower := (rows 25 35 134 104 274 36 68 128 256), losses := [] }

theorem u5385 : Upper (D 6) (R 6) [24,33,130,96,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5386 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 25 35 164 13 274 96 66 196 324), lower := (rows 25 35 164 13 274 96 66 128 256), losses := [] }

theorem u5386 : Upper (D 6) (R 6) [24,33,160,5,258,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5387 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 7, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 35 164 13 274 96 68 194 322), lower := (rows 25 35 164 13 274 96 68 128 256), losses := [] }

theorem u5387 : Upper (D 6) (R 6) [24,33,160,5,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5388 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 73, targets := 34 }], pairs := [(0,1),(0,5),(3,1)], upper := (rows 25 35 164 76 276 34 65 194 322), lower := (rows 25 35 164 76 276 34 65 128 256), losses := [] }

theorem u5388 : Upper (D 6) (R 6) [24,33,160,68,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5389 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 273, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 35 164 76 276 34 66 193 321), lower := (rows 25 35 164 76 276 34 66 128 256), losses := [] }

theorem u5389 : Upper (D 6) (R 6) [24,33,160,68,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5390 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 81, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 25 35 196 14 82 288 65 164 292), lower := (rows 25 35 196 14 82 288 65 128 256), losses := [] }

theorem u5390 : Upper (D 6) (R 6) [24,33,192,6,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5390 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5391 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 25 35 196 14 82 288 68 161 289), lower := (rows 25 35 196 14 82 288 68 128 256), losses := [] }

theorem u5391 : Upper (D 6) (R 6) [24,33,192,6,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5391 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5392 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 25 35 196 14 82 288 96 133 261), lower := (rows 25 35 196 14 82 288 96 128 256), losses := [] }

theorem u5392 : Upper (D 6) (R 6) [24,33,192,6,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5392 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5393 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 25 35 196 14 273 96 66 164 292), lower := (rows 25 35 196 14 273 96 66 128 256), losses := [] }

theorem u5393 : Upper (D 6) (R 6) [24,33,192,6,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5394 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 1, region := 272, targets := 4 }], pairs := [(2,0),(3,0),(4,2)], upper := (rows 25 35 196 14 273 96 68 162 290), lower := (rows 25 35 196 14 273 96 68 128 256), losses := [] }

theorem u5394 : Upper (D 6) (R 6) [24,33,192,6,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5395 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 273, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 35 196 14 273 96 96 134 262), lower := (rows 25 35 196 14 273 96 96 128 256), losses := [] }

theorem u5395 : Upper (D 6) (R 6) [24,33,192,6,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5396 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 3 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 25 35 196 14 274 96 65 164 292), lower := (rows 25 35 196 14 274 96 65 128 256), losses := [] }

theorem u5396 : Upper (D 6) (R 6) [24,33,192,6,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5397 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 272, targets := 68 },{ cop := 7, region := 68, targets := 1 }], pairs := [(2,0),(4,2),(4,6)], upper := (rows 25 35 196 14 274 96 68 161 289), lower := (rows 25 35 196 14 274 96 68 128 256), losses := [] }

theorem u5397 : Upper (D 6) (R 6) [24,33,192,6,258,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5398 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 273, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 35 196 14 274 96 96 133 261), lower := (rows 25 35 196 14 274 96 96 128 256), losses := [] }

theorem u5398 : Upper (D 6) (R 6) [24,33,192,6,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5399 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 204, targets := 32 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,5),(3,5)], upper := (rows 25 35 196 14 304 96 65 134 262), lower := (rows 25 35 196 14 304 96 65 128 256), losses := [] }

theorem u5399 : Upper (D 6) (R 6) [24,33,192,6,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5399
end Delivery.IrregularNine14.P06
