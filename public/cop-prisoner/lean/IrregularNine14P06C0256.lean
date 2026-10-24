import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0059
import IrregularNine14P06C0060

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r15360 : Route 9 := (fun mask => (mask,id))

def c15360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15360 : Upper (D 6) (R 6) [10,129,34,48,68,256] 13 := by
  apply FastRouting.sound _ _ [10,129,34,48,68,256] 13 (by decide) (choices 1) [1,4] r15360 c15360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3557
  · exact u3558

def b15361 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 36, targets := 1 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 56 273 36 68 196 324), lower := (rows 11 131 38 56 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 119 183 311), good := (rows 494 486 486 504 508 484 64 128 256) }] }

theorem u15361 : Upper (D 6) (R 6) [10,129,34,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15362 : Route 9 := (fun mask => (mask,id))

def c15362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15362 : Upper (D 6) (R 6) [10,129,34,48,257,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,48,257,64] 13 (by decide) (choices 1) [4] r15362 c15362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u3559

def b15363 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 56 276 33 68 196 324), lower := (rows 11 131 38 56 276 33 64 128 256), losses := [] }

theorem u15363 : Upper (D 6) (R 6) [10,129,34,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15364 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 195, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 131 38 56 276 36 65 193 321), lower := (rows 11 131 38 56 276 36 64 128 256), losses := [] }

theorem u15364 : Upper (D 6) (R 6) [10,129,34,48,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15365 : Route 9 := (fun mask => (mask,id))

def c15365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15365 : Upper (D 6) (R 6) [10,129,34,48,260,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,48,260,64] 13 (by decide) (choices 1) [1,4] r15365 c15365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3560
  · exact u3561

def b15366 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 56 336 33 68 196 324), lower := (rows 11 131 38 56 336 33 64 128 256), losses := [] }

theorem u15366 : Upper (D 6) (R 6) [10,129,34,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15367 : Route 9 := (fun mask => (mask,id))

def c15367 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15367 : Upper (D 6) (R 6) [10,129,34,48,320,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,48,320,4] 13 (by decide) (choices 1) [1,4] r15367 c15367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3562
  · exact u3563

def b15368 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 38 56 336 96 69 133 261), lower := (rows 11 131 38 56 336 96 64 128 256), losses := [] }

theorem u15368 : Upper (D 6) (R 6) [10,129,34,48,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15369 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 4, region := 450, targets := 4 }], pairs := [(1,2),(2,6),(4,6)], upper := (rows 11 131 38 76 49 36 336 464 336), lower := (rows 11 131 38 76 49 36 64 128 256), losses := [] }

theorem u15369 : Upper (D 6) (R 6) [10,129,34,68,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15370 : PairBound 9 := { available := 324, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 38 76 49 48 324 452 324), lower := (rows 11 131 38 76 49 48 64 128 256), losses := [] }

theorem u15370 : Upper (D 6) (R 6) [10,129,34,68,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15370 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15371 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 390, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 131 38 76 49 96 340 404 276), lower := (rows 11 131 38 76 49 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 5 24 16 120 80 144 272), good := (rows 46 134 38 108 508 96 96 128 256) }] }

theorem u15371 : Upper (D 6) (R 6) [10,129,34,68,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15372 : Route 9 := (fun mask => (mask,id))

def c15372 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15372 : Upper (D 6) (R 6) [10,129,34,68,33,256] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,33,256] 13 (by decide) (choices 1) [4,16] r15372 c15372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3564
  · exact u3565

def b15373 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 131 38 76 81 36 368 432 304), lower := (rows 11 131 38 76 81 36 64 128 256), losses := [] }

theorem u15373 : Upper (D 6) (R 6) [10,129,34,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15374 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 328, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 76 81 48 356 420 292), lower := (rows 11 131 38 76 81 48 64 128 256), losses := [] }

theorem u15374 : Upper (D 6) (R 6) [10,129,34,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15374 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15375 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 131 38 76 81 288 116 180 308), lower := (rows 11 131 38 76 81 288 64 128 256), losses := [] }

theorem u15375 : Upper (D 6) (R 6) [10,129,34,68,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15375 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15376 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 76 112 33 340 404 276), lower := (rows 11 131 38 76 112 33 64 128 256), losses := [] }

theorem u15376 : Upper (D 6) (R 6) [10,129,34,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15377 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 3, region := 48, targets := 1 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 131 38 76 112 36 337 401 273), lower := (rows 11 131 38 76 112 36 64 128 256), losses := [] }

theorem u15377 : Upper (D 6) (R 6) [10,129,34,68,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15378 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 131 38 76 112 48 325 389 261), lower := (rows 11 131 38 76 112 48 64 128 256), losses := [] }

theorem u15378 : Upper (D 6) (R 6) [10,129,34,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15378 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15379 : Route 9 := (fun mask => (mask,id))

def c15379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15379 : Upper (D 6) (R 6) [10,129,34,68,96,256] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,96,256] 13 (by decide) (choices 1) [1,4,16] r15379 c15379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3566
  · exact u3567
  · exact u3568

def b15380 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 76 273 36 112 240 368), lower := (rows 11 131 38 76 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 63 80 144 272), good := (rows 46 166 38 108 508 36 64 128 256) }] }

theorem u15380 : Upper (D 6) (R 6) [10,129,34,68,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15381 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 76 273 48 100 228 356), lower := (rows 11 131 38 76 273 48 64 128 256), losses := [] }

theorem u15381 : Upper (D 6) (R 6) [10,129,34,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15381 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15382 : Route 9 := (fun mask => (mask,id))

def c15382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15382 : Upper (D 6) (R 6) [10,129,34,68,257,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,257,64] 13 (by decide) (choices 1) [4,16,32] r15382 c15382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3569
  · exact u3570
  · exact u3571

def b15383 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 76 276 33 112 240 368), lower := (rows 11 131 38 76 276 33 64 128 256), losses := [] }

theorem u15383 : Upper (D 6) (R 6) [10,129,34,68,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15384 : Route 9 := (fun mask => (mask,id))

def c15384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15384 : Upper (D 6) (R 6) [10,129,34,68,260,16] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,260,16] 13 (by decide) (choices 1) [1,32] r15384 c15384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3572
  · exact u3573

def r15385 : Route 9 := (fun mask => (mask,id))

def c15385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15385 : Upper (D 6) (R 6) [10,129,34,68,260,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,260,64] 13 (by decide) (choices 1) [1,16,32] r15385 c15385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3574
  · exact u3575
  · exact u3576

def b15386 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 76 304 33 84 212 340), lower := (rows 11 131 38 76 304 33 64 128 256), losses := [] }

theorem u15386 : Upper (D 6) (R 6) [10,129,34,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15387 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,1)], upper := (rows 11 131 38 76 304 36 81 209 337), lower := (rows 11 131 38 76 304 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 21 44 67 131 259), good := (rows 505 465 508 124 304 60 64 128 256) }] }

theorem u15387 : Upper (D 6) (R 6) [10,129,34,68,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15388 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 131 38 76 304 48 69 197 325), lower := (rows 11 131 38 76 304 48 64 128 256), losses := [] }

theorem u15388 : Upper (D 6) (R 6) [10,129,34,68,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15388 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15389 : Route 9 := (fun mask => (mask,id))

def c15389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15389 : Upper (D 6) (R 6) [10,129,34,68,288,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,288,64] 13 (by decide) (choices 1) [1,4,16] r15389 c15389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3577
  · exact u3578
  · exact u3579

def b15390 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 76 336 33 116 180 308), lower := (rows 11 131 38 76 336 33 64 128 256), losses := [] }

theorem u15390 : Upper (D 6) (R 6) [10,129,34,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15391 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(4,1)], upper := (rows 11 131 38 76 336 36 113 177 305), lower := (rows 11 131 38 76 336 36 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 19 44 65 129 257), good := (rows 505 465 52 108 336 36 64 128 256) }] }

theorem u15391 : Upper (D 6) (R 6) [10,129,34,68,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15392 : Route 9 := (fun mask => (mask,id))

def c15392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15392 : Upper (D 6) (R 6) [10,129,34,68,320,16] 13 := by
  apply FastRouting.sound _ _ [10,129,34,68,320,16] 13 (by decide) (choices 1) [1,4,32] r15392 c15392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3580
  · exact u3581
  · exact u3582

def b15393 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 52, targets := 64 },{ cop := 0, region := 36, targets := 1 }], pairs := [(2,0),(2,6),(4,6)], upper := (rows 11 131 38 88 49 36 324 452 324), lower := (rows 11 131 38 88 49 36 64 128 256), losses := [] }

theorem u15393 : Upper (D 6) (R 6) [10,129,34,80,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15394 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 390, targets := 64 },{ cop := 0, region := 356, targets := 1 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 131 38 88 49 96 324 388 260), lower := (rows 11 131 38 88 49 96 64 128 256), losses := [] }

theorem u15394 : Upper (D 6) (R 6) [10,129,34,80,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15395 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 356, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 131 38 88 49 288 68 196 324), lower := (rows 11 131 38 88 49 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 319 87 151 279), good := (rows 494 486 486 504 508 288 64 128 288) }] }

theorem u15395 : Upper (D 6) (R 6) [10,129,34,80,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15395 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15396 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 36, targets := 1 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 88 273 36 100 228 356), lower := (rows 11 131 38 88 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 119 183 311), good := (rows 494 486 486 504 508 484 64 128 256) }] }

theorem u15396 : Upper (D 6) (R 6) [10,129,34,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15397 : Route 9 := (fun mask => (mask,id))

def c15397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15397 : Upper (D 6) (R 6) [10,129,34,80,257,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,80,257,64] 13 (by decide) (choices 1) [4,32] r15397 c15397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3583
  · exact u3584

def b15398 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 88 276 33 100 228 356), lower := (rows 11 131 38 88 276 33 64 128 256), losses := [] }

theorem u15398 : Upper (D 6) (R 6) [10,129,34,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15399 : Route 9 := (fun mask => (mask,id))

def c15399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15399 : Upper (D 6) (R 6) [10,129,34,80,260,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,80,260,4] 13 (by decide) (choices 1) [1,32] r15399 c15399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3585
  · exact u3586

def r15400 : Route 9 := (fun mask => (mask,id))

def c15400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15400 : Upper (D 6) (R 6) [10,129,34,80,260,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,80,260,64] 13 (by decide) (choices 1) [1,4,32] r15400 c15400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3587
  · exact u3588
  · exact u3589

def b15401 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 88 304 33 68 196 324), lower := (rows 11 131 38 88 304 33 64 128 256), losses := [] }

theorem u15401 : Upper (D 6) (R 6) [10,129,34,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15402 : Route 9 := (fun mask => (mask,id))

def c15402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15402 : Upper (D 6) (R 6) [10,129,34,80,288,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,80,288,4] 13 (by decide) (choices 1) [1,4] r15402 c15402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3590
  · exact u3591

def r15403 : Route 9 := (fun mask => (mask,id))

def c15403 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15403 : Upper (D 6) (R 6) [10,129,34,80,288,64] 13 := by
  apply FastRouting.sound _ _ [10,129,34,80,288,64] 13 (by decide) (choices 1) [1,4] r15403 c15403
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3592
  · exact u3593

def b15404 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,0),(2,6)], upper := (rows 11 131 38 104 81 36 340 404 276), lower := (rows 11 131 38 104 81 36 64 128 256), losses := [] }

theorem u15404 : Upper (D 6) (R 6) [10,129,34,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15405 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 38 104 81 48 324 388 260), lower := (rows 11 131 38 104 81 48 64 128 256), losses := [] }

theorem u15405 : Upper (D 6) (R 6) [10,129,34,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15405 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15406 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 131 38 104 81 288 84 148 276), lower := (rows 11 131 38 104 81 288 64 128 256), losses := [] }

theorem u15406 : Upper (D 6) (R 6) [10,129,34,96,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15406 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15407 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 104 84 33 340 404 276), lower := (rows 11 131 38 104 84 33 64 128 256), losses := [] }

theorem u15407 : Upper (D 6) (R 6) [10,129,34,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15408 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 36, targets := 65 },{ cop := 4, region := 40, targets := 1 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 104 84 36 337 401 273), lower := (rows 11 131 38 104 84 36 64 128 256), losses := [] }

theorem u15408 : Upper (D 6) (R 6) [10,129,34,96,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15409 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 131 38 104 84 48 325 389 261), lower := (rows 11 131 38 104 84 48 64 128 256), losses := [] }

theorem u15409 : Upper (D 6) (R 6) [10,129,34,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15409 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15410 : Route 9 := (fun mask => (mask,id))

def c15410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15410 : Upper (D 6) (R 6) [10,129,34,96,68,256] 13 := by
  apply FastRouting.sound _ _ [10,129,34,96,68,256] 13 (by decide) (choices 1) [1,4,16] r15410 c15410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3594
  · exact u3595
  · exact u3596

def b15411 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 36, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 11 131 38 104 273 36 84 212 340), lower := (rows 11 131 38 104 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 55 80 144 272), good := (rows 46 166 38 104 508 36 64 128 256) }] }

theorem u15411 : Upper (D 6) (R 6) [10,129,34,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15412 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 38 104 273 48 68 196 324), lower := (rows 11 131 38 104 273 48 64 128 256), losses := [] }

theorem u15412 : Upper (D 6) (R 6) [10,129,34,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15412 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15413 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 38 104 273 96 84 148 276), lower := (rows 11 131 38 104 273 96 64 128 256), losses := [] }

theorem u15413 : Upper (D 6) (R 6) [10,129,34,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15414 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 104 276 33 84 212 340), lower := (rows 11 131 38 104 276 33 64 128 256), losses := [] }

theorem u15414 : Upper (D 6) (R 6) [10,129,34,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15415 : Route 9 := (fun mask => (mask,id))

def c15415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15415 : Upper (D 6) (R 6) [10,129,34,96,260,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,96,260,4] 13 (by decide) (choices 1) [1,16] r15415 c15415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3597
  · exact u3598

def r15416 : Route 9 := (fun mask => (mask,id))

def c15416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15416 : Upper (D 6) (R 6) [10,129,34,96,260,16] 13 := by
  apply FastRouting.sound _ _ [10,129,34,96,260,16] 13 (by decide) (choices 1) [1,4] r15416 c15416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3599
  · exact u3600

def b15417 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 131 38 104 276 96 85 149 277), lower := (rows 11 131 38 104 276 96 64 128 256), losses := [] }

theorem u15417 : Upper (D 6) (R 6) [10,129,34,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b15418 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 38 104 336 33 84 148 276), lower := (rows 11 131 38 104 336 33 64 128 256), losses := [] }

theorem u15418 : Upper (D 6) (R 6) [10,129,34,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b15418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r15419 : Route 9 := (fun mask => (mask,id))

def c15419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u15419 : Upper (D 6) (R 6) [10,129,34,96,320,4] 13 := by
  apply FastRouting.sound _ _ [10,129,34,96,320,4] 13 (by decide) (choices 1) [1,4,16] r15419 c15419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3601
  · exact u3602
  · exact u3603

#print axioms u15419
end Delivery.IrregularNine14.P06
