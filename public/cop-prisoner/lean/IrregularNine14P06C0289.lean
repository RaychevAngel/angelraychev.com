import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0077
import IrregularNine14P06C0078

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b17340 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 69 268 112 48 71 135 263), lower := (rows 11 162 69 268 112 48 64 128 256), losses := [] }

theorem u17340 : Upper (D 6) (R 6) [10,160,65,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17340 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17341 : Route 9 := (fun mask => (mask,id))

def c17341 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17341 : Upper (D 6) (R 6) [10,160,65,272,6,1] 13 := by
  apply FastRouting.sound _ _ [10,160,65,272,6,1] 13 (by decide) (choices 1) [4,32] r17341 c17341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4649
  · exact u4650

def r17342 : Route 9 := (fun mask => (mask,id))

def c17342 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17342 : Upper (D 6) (R 6) [10,160,65,272,6,4] 13 := by
  apply FastRouting.sound _ _ [10,160,65,272,6,4] 13 (by decide) (choices 1) [1,32] r17342 c17342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4651
  · exact u4652

def r17343 : Route 9 := (fun mask => (mask,id))

def c17343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17343 : Upper (D 6) (R 6) [10,160,65,272,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,65,272,6,64] 13 (by decide) (choices 1) [1,4,32] r17343 c17343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4653
  · exact u4654
  · exact u4655

def b17344 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 162 69 280 52 33 70 198 326), lower := (rows 11 162 69 280 52 33 64 128 256), losses := [] }

theorem u17344 : Upper (D 6) (R 6) [10,160,65,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17345 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 280 52 34 69 197 325), lower := (rows 11 162 69 280 52 34 64 128 256), losses := [] }

theorem u17345 : Upper (D 6) (R 6) [10,160,65,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17346 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 162 69 280 52 36 67 195 323), lower := (rows 11 162 69 280 52 36 64 128 256), losses := [] }

theorem u17346 : Upper (D 6) (R 6) [10,160,65,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17346 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17347 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 69 280 52 96 71 135 263), lower := (rows 11 162 69 280 52 96 64 128 256), losses := [] }

theorem u17347 : Upper (D 6) (R 6) [10,160,65,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17347 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17348 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 2, region := 162, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 11 162 69 280 82 33 100 164 292), lower := (rows 11 162 69 280 82 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 37 24 16 37 103 167 295), good := (rows 493 484 485 280 472 485 64 128 256) }] }

theorem u17348 : Upper (D 6) (R 6) [10,160,65,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17349 : Route 9 := (fun mask => (mask,id))

def c17349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17349 : Upper (D 6) (R 6) [10,160,65,272,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,65,272,66,4] 13 (by decide) (choices 1) [1,4,32] r17349 c17349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4656
  · exact u4657
  · exact u4658

def b17350 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 68, targets := 32 },{ cop := 2, region := 48, targets := 2 },{ cop := 2, region := 48, targets := 4 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 162 69 280 112 33 70 134 262), lower := (rows 11 162 69 280 112 33 64 128 256), losses := [] }

theorem u17350 : Upper (D 6) (R 6) [10,160,65,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17351 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 280 112 34 69 133 261), lower := (rows 11 162 69 280 112 34 64 128 256), losses := [] }

theorem u17351 : Upper (D 6) (R 6) [10,160,65,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17352 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 162 69 280 112 36 71 135 263), lower := (rows 11 162 69 280 112 36 64 128 256), losses := [] }

theorem u17352 : Upper (D 6) (R 6) [10,160,65,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17353 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 69 296 22 33 84 212 340), lower := (rows 11 162 69 296 22 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 80 144 272), good := (rows 41 160 101 296 508 33 64 128 256) }] }

theorem u17353 : Upper (D 6) (R 6) [10,160,65,288,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17353 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17354 : Route 9 := (fun mask => (mask,id))

def c17354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17354 : Upper (D 6) (R 6) [10,160,65,288,6,4] 13 := by
  apply FastRouting.sound _ _ [10,160,65,288,6,4] 13 (by decide) (choices 1) [1,16] r17354 c17354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4659
  · exact u4660

def b17355 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 296 22 48 69 197 325), lower := (rows 11 162 69 296 22 48 64 128 256), losses := [] }

theorem u17355 : Upper (D 6) (R 6) [10,160,65,288,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17355 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17356 : Route 9 := (fun mask => (mask,id))

def c17356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17356 : Upper (D 6) (R 6) [10,160,65,288,6,64] 13 := by
  apply FastRouting.sound _ _ [10,160,65,288,6,64] 13 (by decide) (choices 1) [1,4,16] r17356 c17356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4661
  · exact u4662
  · exact u4663

def r17357 : Route 9 := (fun mask => (mask,id))

def c17357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17357 : Upper (D 6) (R 6) [10,160,65,288,66,1] 13 := by
  apply FastRouting.sound _ _ [10,160,65,288,66,1] 13 (by decide) (choices 1) [4,16] r17357 c17357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4664
  · exact u4665

def r17358 : Route 9 := (fun mask => (mask,id))

def c17358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17358 : Upper (D 6) (R 6) [10,160,65,288,66,4] 13 := by
  apply FastRouting.sound _ _ [10,160,65,288,66,4] 13 (by decide) (choices 1) [1,4,16] r17358 c17358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4666
  · exact u4667
  · exact u4668

def b17359 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 69 296 82 48 69 133 261), lower := (rows 11 162 69 296 82 48 64 128 256), losses := [] }

theorem u17359 : Upper (D 6) (R 6) [10,160,65,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17359 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17360 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 178, targets := 64 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 11 162 69 328 22 33 116 180 308), lower := (rows 11 162 69 328 22 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 80 144 272), good := (rows 41 160 101 328 508 33 64 128 256) }] }

theorem u17360 : Upper (D 6) (R 6) [10,160,65,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17361 : Route 9 := (fun mask => (mask,id))

def c17361 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17361 : Upper (D 6) (R 6) [10,160,65,320,6,4] 13 := by
  apply FastRouting.sound _ _ [10,160,65,320,6,4] 13 (by decide) (choices 1) [1,16,32] r17361 c17361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4669
  · exact u4670
  · exact u4671

def b17362 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 178, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 11 162 69 328 22 48 101 165 293), lower := (rows 11 162 69 328 22 48 64 128 256), losses := [] }

theorem u17362 : Upper (D 6) (R 6) [10,160,65,320,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17362 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17363 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 332, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 162 69 328 49 34 84 148 276), lower := (rows 11 162 69 328 49 34 64 128 256), losses := [] }

theorem u17363 : Upper (D 6) (R 6) [10,160,65,320,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17364 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 178, targets := 64 },{ cop := 2, region := 48, targets := 2 }], pairs := [(1,6),(4,1),(4,6)], upper := (rows 11 162 69 328 49 36 86 150 278), lower := (rows 11 162 69 328 49 36 64 128 256), losses := [] }

theorem u17364 : Upper (D 6) (R 6) [10,160,65,320,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17365 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 162 69 328 49 48 70 134 262), lower := (rows 11 162 69 328 49 48 64 128 256), losses := [] }

theorem u17365 : Upper (D 6) (R 6) [10,160,65,320,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17365 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17366 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 178, targets := 64 },{ cop := 4, region := 130, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 11 162 69 328 52 33 86 150 278), lower := (rows 11 162 69 328 52 33 64 128 256), losses := [] }

theorem u17366 : Upper (D 6) (R 6) [10,160,65,320,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17367 : PairBound 9 := { available := 21, camps := [{ cop := 7, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 162 69 328 52 34 85 149 277), lower := (rows 11 162 69 328 52 34 64 128 256), losses := [] }

theorem u17367 : Upper (D 6) (R 6) [10,160,65,320,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17368 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 459, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 69 328 52 36 83 147 275), lower := (rows 11 162 69 328 52 36 64 128 256), losses := [] }

theorem u17368 : Upper (D 6) (R 6) [10,160,65,320,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17369 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 333, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 162 69 328 52 48 71 135 263), lower := (rows 11 162 69 328 52 48 64 128 256), losses := [] }

theorem u17369 : Upper (D 6) (R 6) [10,160,65,320,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17369 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17370 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 162 70 25 52 33 324 452 324), lower := (rows 11 162 70 25 52 33 64 128 256), losses := [] }

theorem u17370 : Upper (D 6) (R 6) [10,160,66,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17371 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 162 70 25 52 36 321 449 321), lower := (rows 11 162 70 25 52 36 64 128 256), losses := [] }

theorem u17371 : Upper (D 6) (R 6) [10,160,66,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17372 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 70 25 52 96 325 389 261), lower := (rows 11 162 70 25 52 96 64 128 256), losses := [] }

theorem u17372 : Upper (D 6) (R 6) [10,160,66,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17373 : Route 9 := (fun mask => (mask,id))

def c17373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17373 : Upper (D 6) (R 6) [10,160,66,17,36,256] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17,36,256] 13 (by decide) (choices 1) [1,4] r17373 c17373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4672
  · exact u4673

def b17374 : PairBound 9 := { available := 260, camps := [{ cop := 2, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 162 70 25 112 33 324 388 260), lower := (rows 11 162 70 25 112 33 64 128 256), losses := [] }

theorem u17374 : Upper (D 6) (R 6) [10,160,66,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17375 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 48, targets := 3 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 162 70 25 112 36 325 389 261), lower := (rows 11 162 70 25 112 36 64 128 256), losses := [] }

theorem u17375 : Upper (D 6) (R 6) [10,160,66,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17376 : Route 9 := (fun mask => (mask,id))

def c17376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17376 : Upper (D 6) (R 6) [10,160,66,17,96,256] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17,96,256] 13 (by decide) (choices 1) [1,4] r17376 c17376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4674
  · exact u4675

def b17377 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 70 25 276 33 100 228 356), lower := (rows 11 162 70 25 276 33 64 128 256), losses := [] }

theorem u17377 : Upper (D 6) (R 6) [10,160,66,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17378 : Route 9 := (fun mask => (mask,id))

def c17378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17378 : Upper (D 6) (R 6) [10,160,66,17,260,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17,260,4] 13 (by decide) (choices 1) [1,32] r17378 c17378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4676
  · exact u4677

def r17379 : Route 9 := (fun mask => (mask,id))

def c17379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17379 : Upper (D 6) (R 6) [10,160,66,17,260,64] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17,260,64] 13 (by decide) (choices 1) [1,4,32] r17379 c17379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4678
  · exact u4679
  · exact u4680

def b17380 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 70 25 304 33 68 196 324), lower := (rows 11 162 70 25 304 33 64 128 256), losses := [] }

theorem u17380 : Upper (D 6) (R 6) [10,160,66,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17381 : Route 9 := (fun mask => (mask,id))

def c17381 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17381 : Upper (D 6) (R 6) [10,160,66,17,288,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17,288,4] 13 (by decide) (choices 1) [1,4] r17381 c17381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4681
  · exact u4682

def r17382 : Route 9 := (fun mask => (mask,id))

def c17382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17382 : Upper (D 6) (R 6) [10,160,66,17,288,64] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17,288,64] 13 (by decide) (choices 1) [1,4] r17382 c17382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4683
  · exact u4684

def b17383 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 70 25 336 33 100 164 292), lower := (rows 11 162 70 25 336 33 64 128 256), losses := [] }

theorem u17383 : Upper (D 6) (R 6) [10,160,66,17,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17384 : Route 9 := (fun mask => (mask,id))

def c17384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17384 : Upper (D 6) (R 6) [10,160,66,17,320,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,17,320,4] 13 (by decide) (choices 1) [1,4,32] r17384 c17384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4685
  · exact u4686
  · exact u4687

def b17385 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 162 70 28 49 33 324 452 324), lower := (rows 11 162 70 28 49 33 64 128 256), losses := [] }

theorem u17385 : Upper (D 6) (R 6) [10,160,66,20,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17386 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 162 70 28 49 36 321 449 321), lower := (rows 11 162 70 28 49 36 64 128 256), losses := [] }

theorem u17386 : Upper (D 6) (R 6) [10,160,66,20,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17387 : Route 9 := (fun mask => (mask,id))

def c17387 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u17387 : Upper (D 6) (R 6) [10,160,66,20,33,64] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20,33,64] 13 (by decide) (choices 1) [1,4,256] r17387 c17387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4688
  · exact u4689
  · exact u4690

def b17388 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 11 162 70 28 49 288 69 197 325), lower := (rows 11 162 70 28 49 288 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 24 16 0 81 145 273), good := (rows 463 130 70 476 477 256 64 128 256) }] }

theorem u17388 : Upper (D 6) (R 6) [10,160,66,20,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17388 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17389 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 70 28 273 33 100 228 356), lower := (rows 11 162 70 28 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 39 24 16 32 98 162 290), good := (rows 462 486 454 28 284 486 64 128 256) }] }

theorem u17389 : Upper (D 6) (R 6) [10,160,66,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r17390 : Route 9 := (fun mask => (mask,id))

def c17390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17390 : Upper (D 6) (R 6) [10,160,66,20,257,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20,257,4] 13 (by decide) (choices 1) [1,32] r17390 c17390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4691
  · exact u4692

def r17391 : Route 9 := (fun mask => (mask,id))

def c17391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17391 : Upper (D 6) (R 6) [10,160,66,20,257,64] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20,257,64] 13 (by decide) (choices 1) [1,4,32] r17391 c17391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4693
  · exact u4694
  · exact u4695

def r17392 : Route 9 := (fun mask => (mask,id))

def c17392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17392 : Upper (D 6) (R 6) [10,160,66,20,288,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20,288,1] 13 (by decide) (choices 1) [1,4] r17392 c17392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4696
  · exact u4697

def r17393 : Route 9 := (fun mask => (mask,id))

def c17393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17393 : Upper (D 6) (R 6) [10,160,66,20,288,4] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20,288,4] 13 (by decide) (choices 1) [1] r17393 c17393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u4698

def r17394 : Route 9 := (fun mask => (mask,id))

def c17394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17394 : Upper (D 6) (R 6) [10,160,66,20,288,64] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20,288,64] 13 (by decide) (choices 1) [1,4] r17394 c17394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4699
  · exact u4700

def r17395 : Route 9 := (fun mask => (mask,id))

def c17395 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u17395 : Upper (D 6) (R 6) [10,160,66,20,320,1] 13 := by
  apply FastRouting.sound _ _ [10,160,66,20,320,1] 13 (by decide) (choices 1) [1,4,32] r17395 c17395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4701
  · exact u4702
  · exact u4703

def b17396 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(4,1)], upper := (rows 11 162 70 28 336 36 97 161 289), lower := (rows 11 162 70 28 336 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 65 129 257), good := (rows 505 160 100 60 336 36 64 128 256) }] }

theorem u17396 : Upper (D 6) (R 6) [10,160,66,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17397 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 41, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 11 162 70 44 81 33 340 404 276), lower := (rows 11 162 70 44 81 33 64 128 256), losses := [] }

theorem u17397 : Upper (D 6) (R 6) [10,160,66,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17398 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 467, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 162 70 44 81 36 337 401 273), lower := (rows 11 162 70 44 81 36 64 128 256), losses := [] }

theorem u17398 : Upper (D 6) (R 6) [10,160,66,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b17399 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 162 70 44 81 48 325 389 261), lower := (rows 11 162 70 44 81 48 64 128 256), losses := [] }

theorem u17399 : Upper (D 6) (R 6) [10,160,66,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b17399 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u17399
end Delivery.IrregularNine14.P06
