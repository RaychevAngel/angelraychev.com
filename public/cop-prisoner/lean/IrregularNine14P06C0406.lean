import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0125

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b24360 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 138 292 13 84 48 67 195 323), lower := (rows 35 138 292 13 84 48 64 128 256), losses := [] }

theorem u24360 : Upper (D 6) (R 6) [34,136,288,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24360 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24361 : Route 9 := (fun mask => (mask,id))

def c24361 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24361 : Upper (D 6) (R 6) [34,136,288,5,68,64] 13 := by
  apply FastRouting.sound _ _ [34,136,288,5,68,64] 13 (by decide) (choices 1) [1,2,16] r24361 c24361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7513
  · exact u7514
  · exact u7515

def b24362 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 292 14 81 33 84 212 340), lower := (rows 35 138 292 14 81 33 64 128 256), losses := [] }

theorem u24362 : Upper (D 6) (R 6) [34,136,288,6,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24363 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 14 81 36 81 209 337), lower := (rows 35 138 292 14 81 36 64 128 256), losses := [] }

theorem u24363 : Upper (D 6) (R 6) [34,136,288,6,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24364 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 292 14 81 48 69 197 325), lower := (rows 35 138 292 14 81 48 64 128 256), losses := [] }

theorem u24364 : Upper (D 6) (R 6) [34,136,288,6,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24364 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24365 : Route 9 := (fun mask => (mask,id))

def c24365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24365 : Upper (D 6) (R 6) [34,136,288,6,65,64] 13 := by
  apply FastRouting.sound _ _ [34,136,288,6,65,64] 13 (by decide) (choices 1) [1,4,16] r24365 c24365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7516
  · exact u7517
  · exact u7518

def b24366 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 292 14 84 33 81 209 337), lower := (rows 35 138 292 14 84 33 64 128 256), losses := [] }

theorem u24366 : Upper (D 6) (R 6) [34,136,288,6,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24367 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 292 14 84 48 65 193 321), lower := (rows 35 138 292 14 84 48 64 128 256), losses := [] }

theorem u24367 : Upper (D 6) (R 6) [34,136,288,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24367 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24368 : Route 9 := (fun mask => (mask,id))

def c24368 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24368 : Upper (D 6) (R 6) [34,136,288,6,68,64] 13 := by
  apply FastRouting.sound _ _ [34,136,288,6,68,64] 13 (by decide) (choices 1) [1,16] r24368 c24368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7519
  · exact u7520

def b24369 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 138 292 25 22 33 68 196 324), lower := (rows 35 138 292 25 22 33 64 128 256), losses := [] }

theorem u24369 : Upper (D 6) (R 6) [34,136,288,17,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24370 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 25 22 36 65 193 321), lower := (rows 35 138 292 25 22 36 64 128 256), losses := [] }

theorem u24370 : Upper (D 6) (R 6) [34,136,288,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24371 : Route 9 := (fun mask => (mask,id))

def c24371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24371 : Upper (D 6) (R 6) [34,136,288,17,6,64] 13 := by
  apply FastRouting.sound _ _ [34,136,288,17,6,64] 13 (by decide) (choices 1) [1,4] r24371 c24371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7521
  · exact u7522

def b24372 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 138 292 25 82 33 68 196 324), lower := (rows 35 138 292 25 82 33 64 128 256), losses := [] }

theorem u24372 : Upper (D 6) (R 6) [34,136,288,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24373 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 25 82 36 69 197 325), lower := (rows 35 138 292 25 82 36 64 128 256), losses := [] }

theorem u24373 : Upper (D 6) (R 6) [34,136,288,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24374 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 4 },{ cop := 0, region := 260, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 35 138 292 25 82 96 69 133 261), lower := (rows 35 138 292 25 82 96 64 128 256), losses := [] }

theorem u24374 : Upper (D 6) (R 6) [34,136,288,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24375 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 292 25 84 33 70 198 326), lower := (rows 35 138 292 25 84 33 64 128 256), losses := [] }

theorem u24375 : Upper (D 6) (R 6) [34,136,288,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24376 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 292 25 84 34 69 197 325), lower := (rows 35 138 292 25 84 34 64 128 256), losses := [] }

theorem u24376 : Upper (D 6) (R 6) [34,136,288,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24377 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 25 84 36 67 195 323), lower := (rows 35 138 292 25 84 36 64 128 256), losses := [] }

theorem u24377 : Upper (D 6) (R 6) [34,136,288,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24378 : Route 9 := (fun mask => (mask,id))

def c24378 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24378 : Upper (D 6) (R 6) [34,136,288,17,68,64] 13 := by
  apply FastRouting.sound _ _ [34,136,288,17,68,64] 13 (by decide) (choices 1) [1,2,4] r24378 c24378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7523
  · exact u7524
  · exact u7525

def b24379 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 292 26 81 33 68 196 324), lower := (rows 35 138 292 26 81 33 64 128 256), losses := [] }

theorem u24379 : Upper (D 6) (R 6) [34,136,288,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24380 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 26 81 36 69 197 325), lower := (rows 35 138 292 26 81 36 64 128 256), losses := [] }

theorem u24380 : Upper (D 6) (R 6) [34,136,288,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24381 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 260, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 292 26 81 96 69 133 261), lower := (rows 35 138 292 26 81 96 64 128 256), losses := [] }

theorem u24381 : Upper (D 6) (R 6) [34,136,288,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24382 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 292 26 84 33 69 197 325), lower := (rows 35 138 292 26 84 33 64 128 256), losses := [] }

theorem u24382 : Upper (D 6) (R 6) [34,136,288,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24383 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 26 84 36 65 193 321), lower := (rows 35 138 292 26 84 36 64 128 256), losses := [] }

theorem u24383 : Upper (D 6) (R 6) [34,136,288,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24384 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 260, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 292 26 84 96 69 133 261), lower := (rows 35 138 292 26 84 96 64 128 256), losses := [] }

theorem u24384 : Upper (D 6) (R 6) [34,136,288,18,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24385 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 138 292 28 81 33 70 198 326), lower := (rows 35 138 292 28 81 33 64 128 256), losses := [] }

theorem u24385 : Upper (D 6) (R 6) [34,136,288,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24386 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 292 28 81 34 69 197 325), lower := (rows 35 138 292 28 81 34 64 128 256), losses := [] }

theorem u24386 : Upper (D 6) (R 6) [34,136,288,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24387 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 28 81 36 67 195 323), lower := (rows 35 138 292 28 81 36 64 128 256), losses := [] }

theorem u24387 : Upper (D 6) (R 6) [34,136,288,20,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24388 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 260, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 35 138 292 28 81 96 71 135 263), lower := (rows 35 138 292 28 81 96 64 128 256), losses := [{ target := 6, region := (rows 1 26 5 24 16 32 0 145 273), good := (rows 423 138 292 414 415 32 0 128 256) }] }

theorem u24388 : Upper (D 6) (R 6) [34,136,288,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24389 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 138 292 28 82 33 69 197 325), lower := (rows 35 138 292 28 82 33 64 128 256), losses := [] }

theorem u24389 : Upper (D 6) (R 6) [34,136,288,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24390 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 28 82 36 65 193 321), lower := (rows 35 138 292 28 82 36 64 128 256), losses := [] }

theorem u24390 : Upper (D 6) (R 6) [34,136,288,20,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24391 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 260, targets := 2 },{ cop := 0, region := 260, targets := 64 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 35 138 292 28 82 96 69 133 261), lower := (rows 35 138 292 28 82 96 64 128 256), losses := [] }

theorem u24391 : Upper (D 6) (R 6) [34,136,288,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24392 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 292 73 21 34 84 212 340), lower := (rows 35 138 292 73 21 34 64 128 256), losses := [] }

theorem u24392 : Upper (D 6) (R 6) [34,136,288,65,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24393 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 138 292 73 21 36 82 210 338), lower := (rows 35 138 292 73 21 36 64 128 256), losses := [] }

theorem u24393 : Upper (D 6) (R 6) [34,136,288,65,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24394 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 138 292 73 21 48 70 198 326), lower := (rows 35 138 292 73 21 48 64 128 256), losses := [] }

theorem u24394 : Upper (D 6) (R 6) [34,136,288,65,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24394 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24395 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(2,6),(4,6)], upper := (rows 35 138 292 73 21 96 86 150 278), lower := (rows 35 138 292 73 21 96 64 128 256), losses := [] }

theorem u24395 : Upper (D 6) (R 6) [34,136,288,65,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24396 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 292 73 22 33 84 212 340), lower := (rows 35 138 292 73 22 33 64 128 256), losses := [] }

theorem u24396 : Upper (D 6) (R 6) [34,136,288,65,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24397 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 73 22 36 81 209 337), lower := (rows 35 138 292 73 22 36 64 128 256), losses := [] }

theorem u24397 : Upper (D 6) (R 6) [34,136,288,65,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24398 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 292 73 22 48 69 197 325), lower := (rows 35 138 292 73 22 48 64 128 256), losses := [] }

theorem u24398 : Upper (D 6) (R 6) [34,136,288,65,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24398 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24399 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 276, targets := 64 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 292 73 22 96 85 149 277), lower := (rows 35 138 292 73 22 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 8 16 104 64 128 256), good := (rows 35 171 288 105 19 96 96 128 256) }] }

theorem u24399 : Upper (D 6) (R 6) [34,136,288,65,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24400 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 292 73 82 33 84 148 276), lower := (rows 35 138 292 73 82 33 64 128 256), losses := [] }

theorem u24400 : Upper (D 6) (R 6) [34,136,288,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24401 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 73 82 36 85 149 277), lower := (rows 35 138 292 73 82 36 64 128 256), losses := [] }

theorem u24401 : Upper (D 6) (R 6) [34,136,288,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24402 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 292 73 82 48 69 133 261), lower := (rows 35 138 292 73 82 48 64 128 256), losses := [] }

theorem u24402 : Upper (D 6) (R 6) [34,136,288,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24402 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24403 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 138 292 73 84 33 86 150 278), lower := (rows 35 138 292 73 84 33 64 128 256), losses := [] }

theorem u24403 : Upper (D 6) (R 6) [34,136,288,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24404 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 292 73 84 34 85 149 277), lower := (rows 35 138 292 73 84 34 64 128 256), losses := [] }

theorem u24404 : Upper (D 6) (R 6) [34,136,288,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24405 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 73 84 36 83 147 275), lower := (rows 35 138 292 73 84 36 64 128 256), losses := [] }

theorem u24405 : Upper (D 6) (R 6) [34,136,288,65,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24406 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 260, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 35 138 292 73 84 48 71 135 263), lower := (rows 35 138 292 73 84 48 64 128 256), losses := [{ target := 6, region := (rows 1 10 5 8 16 48 0 137 265), good := (rows 423 394 292 399 52 48 0 128 256) }] }

theorem u24406 : Upper (D 6) (R 6) [34,136,288,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24406 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24407 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 138 292 74 84 33 85 149 277), lower := (rows 35 138 292 74 84 33 64 128 256), losses := [] }

theorem u24407 : Upper (D 6) (R 6) [34,136,288,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24408 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 74 84 36 81 145 273), lower := (rows 35 138 292 74 84 36 64 128 256), losses := [] }

theorem u24408 : Upper (D 6) (R 6) [34,136,288,66,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24409 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 138 292 74 84 48 69 133 261), lower := (rows 35 138 292 74 84 48 64 128 256), losses := [] }

theorem u24409 : Upper (D 6) (R 6) [34,136,288,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24409 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24410 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 202, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 138 292 76 21 33 82 210 338), lower := (rows 35 138 292 76 21 33 64 128 256), losses := [] }

theorem u24410 : Upper (D 6) (R 6) [34,136,288,68,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24411 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 292 76 21 34 81 209 337), lower := (rows 35 138 292 76 21 34 64 128 256), losses := [] }

theorem u24411 : Upper (D 6) (R 6) [34,136,288,68,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24412 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 138 292 76 21 48 67 195 323), lower := (rows 35 138 292 76 21 48 64 128 256), losses := [] }

theorem u24412 : Upper (D 6) (R 6) [34,136,288,68,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24412 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24413 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(2,6),(4,6)], upper := (rows 35 138 292 76 21 96 83 147 275), lower := (rows 35 138 292 76 21 96 64 128 256), losses := [] }

theorem u24413 : Upper (D 6) (R 6) [34,136,288,68,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24414 : Route 9 := (fun mask => (mask,id))

def c24414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24414 : Upper (D 6) (R 6) [34,136,288,68,6,1] 13 := by
  apply FastRouting.sound _ _ [34,136,288,68,6,1] 13 (by decide) (choices 1) [1,16] r24414 c24414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7526
  · exact u7527

def b24415 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 138 292 76 22 48 65 193 321), lower := (rows 35 138 292 76 22 48 64 128 256), losses := [] }

theorem u24415 : Upper (D 6) (R 6) [34,136,288,68,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24415 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24416 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 276, targets := 64 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(2,6),(4,6)], upper := (rows 35 138 292 76 22 96 81 145 273), lower := (rows 35 138 292 76 22 96 64 128 256), losses := [] }

theorem u24416 : Upper (D 6) (R 6) [34,136,288,68,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r24417 : Route 9 := (fun mask => (mask,id))

def c24417 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u24417 : Upper (D 6) (R 6) [34,136,288,68,65,1] 13 := by
  apply FastRouting.sound _ _ [34,136,288,68,65,1] 13 (by decide) (choices 1) [2,4,16] r24417 c24417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7528
  · exact u7529
  · exact u7530

def b24418 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 138 292 76 81 34 85 149 277), lower := (rows 35 138 292 76 81 34 64 128 256), losses := [] }

theorem u24418 : Upper (D 6) (R 6) [34,136,288,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b24419 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 138 292 76 81 36 83 147 275), lower := (rows 35 138 292 76 81 36 64 128 256), losses := [] }

theorem u24419 : Upper (D 6) (R 6) [34,136,288,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b24419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u24419
end Delivery.IrregularNine14.P06
