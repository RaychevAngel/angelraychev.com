import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0258
import IrregularNine14P07C0259
import IrregularNine14P07C0260

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32340 : Route 9 := (fun mask => (mask,id))

def c32340 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32340 : Upper (D 7) (R 7) [12,33,17,320,130] 13 := by
  apply FastRouting.sound _ _ [12,33,17,320,130] 13 (by decide) (choices 1) [2,64,128] r32340 c32340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15538
  · exact u15539
  · exact u15540

def r32341 : Route 9 := (fun mask => (mask,id))

def c32341 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32341 : Upper (D 7) (R 7) [12,33,17,320,160] 13 := by
  apply FastRouting.sound _ _ [12,33,17,320,160] 13 (by decide) (choices 1) [2,64,128] r32341 c32341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15541
  · exact u15542
  · exact u15543

def r32342 : Route 9 := (fun mask => (mask,id))

def c32342 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32342 : Upper (D 7) (R 7) [12,33,17,320,192] 13 := by
  apply FastRouting.sound _ _ [12,33,17,320,192] 13 (by decide) (choices 1) [2,128] r32342 c32342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15544
  · exact u15545

def b32343 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 22 73 50 480 448 448 448), lower := (rows 13 35 22 73 50 32 64 128 256), losses := [] }

theorem u32343 : Upper (D 7) (R 7) [12,33,18,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32344 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 13, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 35 22 73 82 416 480 416 416), lower := (rows 13 35 22 73 82 32 64 128 256), losses := [] }

theorem u32344 : Upper (D 7) (R 7) [12,33,18,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32345 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 73 112 418 450 386 386), lower := (rows 13 35 22 73 112 32 64 128 256), losses := [] }

theorem u32345 : Upper (D 7) (R 7) [12,33,18,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32346 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 35 22 73 146 480 480 480 480), lower := (rows 13 35 22 73 146 32 64 128 256), losses := [] }

theorem u32346 : Upper (D 7) (R 7) [12,33,18,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32347 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,0),(3,5),(4,0)], upper := (rows 13 35 22 73 176 482 450 450 450), lower := (rows 13 35 22 73 176 32 64 128 256), losses := [] }

theorem u32347 : Upper (D 7) (R 7) [12,33,18,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32348 : Route 9 := (fun mask => (mask,id))

def c32348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32348 : Upper (D 7) (R 7) [12,33,18,65,192] 13 := by
  apply FastRouting.sound _ _ [12,33,18,65,192] 13 (by decide) (choices 1) [2,128,256] r32348 c32348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15546
  · exact u15547
  · exact u15548

def b32349 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 35 22 73 274 224 224 224 480), lower := (rows 13 35 22 73 274 32 64 128 256), losses := [] }

theorem u32349 : Upper (D 7) (R 7) [12,33,18,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32350 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 468, targets := 1 },{ cop := 2, region := 201, targets := 32 }], pairs := [(0,5),(2,0),(3,5),(4,0)], upper := (rows 13 35 22 73 304 226 194 194 450), lower := (rows 13 35 22 73 304 32 64 128 256), losses := [] }

theorem u32350 : Upper (D 7) (R 7) [12,33,18,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32351 : Route 9 := (fun mask => (mask,id))

def c32351 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32351 : Upper (D 7) (R 7) [12,33,18,65,320] 13 := by
  apply FastRouting.sound _ _ [12,33,18,65,320] 13 (by decide) (choices 1) [2,128] r32351 c32351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15549
  · exact u15550

def r32352 : Route 9 := (fun mask => (mask,id))

def c32352 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32352 : Upper (D 7) (R 7) [12,33,18,65,384] 13 := by
  apply FastRouting.sound _ _ [12,33,18,65,384] 13 (by decide) (choices 1) [2,64,128] r32352 c32352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15551
  · exact u15552
  · exact u15553

def b32353 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 22 74 49 480 448 448 448), lower := (rows 13 35 22 74 49 32 64 128 256), losses := [] }

theorem u32353 : Upper (D 7) (R 7) [12,33,18,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32354 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 21, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 13 35 22 74 81 416 480 416 416), lower := (rows 13 35 22 74 81 32 64 128 256), losses := [] }

theorem u32354 : Upper (D 7) (R 7) [12,33,18,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32355 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 35 22 74 112 417 449 385 385), lower := (rows 13 35 22 74 112 32 64 128 256), losses := [] }

theorem u32355 : Upper (D 7) (R 7) [12,33,18,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32356 : Route 9 := (fun mask => (mask,id))

def c32356 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32356 : Upper (D 7) (R 7) [12,33,18,66,129] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,129] 13 (by decide) (choices 1) [64,128,256] r32356 c32356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15554
  · exact u15555
  · exact u15556

def r32357 : Route 9 := (fun mask => (mask,id))

def c32357 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32357 : Upper (D 7) (R 7) [12,33,18,66,160] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,160] 13 (by decide) (choices 1) [1,64,128,256] r32357 c32357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15557
  · exact u15558
  · exact u15559
  · exact u15560

def r32358 : Route 9 := (fun mask => (mask,id))

def c32358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32358 : Upper (D 7) (R 7) [12,33,18,66,192] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,192] 13 (by decide) (choices 1) [1,128,256] r32358 c32358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15561
  · exact u15562
  · exact u15563

def r32359 : Route 9 := (fun mask => (mask,id))

def c32359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32359 : Upper (D 7) (R 7) [12,33,18,66,257] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,257] 13 (by decide) (choices 1) [64,128] r32359 c32359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15564
  · exact u15565

def r32360 : Route 9 := (fun mask => (mask,id))

def c32360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32360 : Upper (D 7) (R 7) [12,33,18,66,288] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,288] 13 (by decide) (choices 1) [1,64,128] r32360 c32360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15566
  · exact u15567
  · exact u15568

def r32361 : Route 9 := (fun mask => (mask,id))

def c32361 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32361 : Upper (D 7) (R 7) [12,33,18,66,320] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,320] 13 (by decide) (choices 1) [1,128] r32361 c32361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15569
  · exact u15570

def r32362 : Route 9 := (fun mask => (mask,id))

def c32362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32362 : Upper (D 7) (R 7) [12,33,18,66,384] 13 := by
  apply FastRouting.sound _ _ [12,33,18,66,384] 13 (by decide) (choices 1) [1,64,128] r32362 c32362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15571
  · exact u15572
  · exact u15573

def b32363 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 23, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 13 35 22 104 19 480 448 448 448), lower := (rows 13 35 22 104 19 32 64 128 256), losses := [] }

theorem u32363 : Upper (D 7) (R 7) [12,33,18,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32364 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 22 104 81 418 450 386 386), lower := (rows 13 35 22 104 81 32 64 128 256), losses := [] }

theorem u32364 : Upper (D 7) (R 7) [12,33,18,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32365 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 35 22 104 82 417 449 385 385), lower := (rows 13 35 22 104 82 32 64 128 256), losses := [] }

theorem u32365 : Upper (D 7) (R 7) [12,33,18,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32366 : Route 9 := (fun mask => (mask,id))

def c32366 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u32366 : Upper (D 7) (R 7) [12,33,18,96,129] 13 := by
  apply FastRouting.sound _ _ [12,33,18,96,129] 13 (by decide) (choices 1) [2,64,128,256] r32366 c32366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15574
  · exact u15575
  · exact u15576
  · exact u15577

def b32367 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 35 22 104 146 481 449 449 449), lower := (rows 13 35 22 104 146 32 64 128 256), losses := [] }

theorem u32367 : Upper (D 7) (R 7) [12,33,18,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32368 : Route 9 := (fun mask => (mask,id))

def c32368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32368 : Upper (D 7) (R 7) [12,33,18,96,192] 13 := by
  apply FastRouting.sound _ _ [12,33,18,96,192] 13 (by decide) (choices 1) [1,2,128,256] r32368 c32368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15578
  · exact u15579
  · exact u15580
  · exact u15581

def r32369 : Route 9 := (fun mask => (mask,id))

def c32369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32369 : Upper (D 7) (R 7) [12,33,18,96,257] 13 := by
  apply FastRouting.sound _ _ [12,33,18,96,257] 13 (by decide) (choices 1) [2,64,128] r32369 c32369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15582
  · exact u15583
  · exact u15584

def b32370 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 35 22 104 274 225 193 193 449), lower := (rows 13 35 22 104 274 32 64 128 256), losses := [] }

theorem u32370 : Upper (D 7) (R 7) [12,33,18,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32371 : Route 9 := (fun mask => (mask,id))

def c32371 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32371 : Upper (D 7) (R 7) [12,33,18,96,320] 13 := by
  apply FastRouting.sound _ _ [12,33,18,96,320] 13 (by decide) (choices 1) [1,2,128] r32371 c32371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15585
  · exact u15586
  · exact u15587

def r32372 : Route 9 := (fun mask => (mask,id))

def c32372 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32372 : Upper (D 7) (R 7) [12,33,18,96,384] 13 := by
  apply FastRouting.sound _ _ [12,33,18,96,384] 13 (by decide) (choices 1) [1,2,64,128] r32372 c32372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15588
  · exact u15589
  · exact u15590
  · exact u15591

def b32373 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 20, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(4,5)], upper := (rows 13 35 22 200 19 480 480 480 480), lower := (rows 13 35 22 200 19 32 64 128 256), losses := [] }

theorem u32373 : Upper (D 7) (R 7) [12,33,18,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32374 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 22 200 49 482 450 450 450), lower := (rows 13 35 22 200 49 32 64 128 256), losses := [] }

theorem u32374 : Upper (D 7) (R 7) [12,33,18,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32375 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 20, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(4,0)], upper := (rows 13 35 22 200 50 481 449 449 449), lower := (rows 13 35 22 200 50 32 64 128 256), losses := [] }

theorem u32375 : Upper (D 7) (R 7) [12,33,18,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32376 : Route 9 := (fun mask => (mask,id))

def c32376 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32376 : Upper (D 7) (R 7) [12,33,18,192,65] 13 := by
  apply FastRouting.sound _ _ [12,33,18,192,65] 13 (by decide) (choices 1) [2,128,256] r32376 c32376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15592
  · exact u15593
  · exact u15594

def b32377 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 35 22 200 82 417 481 417 417), lower := (rows 13 35 22 200 82 32 64 128 256), losses := [] }

theorem u32377 : Upper (D 7) (R 7) [12,33,18,192,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32378 : Route 9 := (fun mask => (mask,id))

def c32378 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32378 : Upper (D 7) (R 7) [12,33,18,192,96] 13 := by
  apply FastRouting.sound _ _ [12,33,18,192,96] 13 (by decide) (choices 1) [1,2,128,256] r32378 c32378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15595
  · exact u15596
  · exact u15597
  · exact u15598

def b32379 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 16, targets := 35 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,5)], upper := (rows 13 35 22 200 208 291 355 419 291), lower := (rows 13 35 22 200 208 32 64 128 256), losses := [] }

theorem u32379 : Upper (D 7) (R 7) [12,33,18,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32380 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32380 : Upper (D 7) (R 7) [12,33,18,192,257] 13 := by
  apply FastRouting.sound _ _ [12,33,18,192,257] 13 (by decide) (choices 1) [2,64] r32380 c32380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15599
  · exact u15600

def b32381 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 35 22 200 274 225 225 225 481), lower := (rows 13 35 22 200 274 32 64 128 256), losses := [] }

theorem u32381 : Upper (D 7) (R 7) [12,33,18,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32382 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32382 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32382 : Upper (D 7) (R 7) [12,33,18,192,288] 13 := by
  apply FastRouting.sound _ _ [12,33,18,192,288] 13 (by decide) (choices 1) [1,2,64] r32382 c32382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15601
  · exact u15602
  · exact u15603

def r32383 : Route 9 := (fun mask => (mask,id))

def c32383 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32383 : Upper (D 7) (R 7) [12,33,18,192,320] 13 := by
  apply FastRouting.sound _ _ [12,33,18,192,320] 13 (by decide) (choices 1) [1,2,128] r32383 c32383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15604
  · exact u15605
  · exact u15606

def b32384 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 22 265 50 224 192 192 448), lower := (rows 13 35 22 265 50 32 64 128 256), losses := [] }

theorem u32384 : Upper (D 7) (R 7) [12,33,18,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32385 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 224 },{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 35 22 265 82 224 224 224 480), lower := (rows 13 35 22 265 82 32 64 128 256), losses := [] }

theorem u32385 : Upper (D 7) (R 7) [12,33,18,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32386 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 2, region := 457, targets := 32 }], pairs := [(0,5),(2,0),(3,5),(4,0)], upper := (rows 13 35 22 265 112 226 194 194 450), lower := (rows 13 35 22 265 112 32 64 128 256), losses := [] }

theorem u32386 : Upper (D 7) (R 7) [12,33,18,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32387 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32387 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32387 : Upper (D 7) (R 7) [12,33,18,257,192] 13 := by
  apply FastRouting.sound _ _ [12,33,18,257,192] 13 (by decide) (choices 1) [2,64] r32387 c32387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15607
  · exact u15608

def b32388 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 22 266 49 224 192 192 448), lower := (rows 13 35 22 266 49 32 64 128 256), losses := [] }

theorem u32388 : Upper (D 7) (R 7) [12,33,18,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32389 : Route 9 := (fun mask => (mask,id))

def c32389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32389 : Upper (D 7) (R 7) [12,33,18,258,65] 13 := by
  apply FastRouting.sound _ _ [12,33,18,258,65] 13 (by decide) (choices 1) [64,128] r32389 c32389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15609
  · exact u15610

def r32390 : Route 9 := (fun mask => (mask,id))

def c32390 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32390 : Upper (D 7) (R 7) [12,33,18,258,96] 13 := by
  apply FastRouting.sound _ _ [12,33,18,258,96] 13 (by decide) (choices 1) [1,64,128] r32390 c32390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15611
  · exact u15612
  · exact u15613

def r32391 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32391 : Upper (D 7) (R 7) [12,33,18,258,192] 13 := by
  apply FastRouting.sound _ _ [12,33,18,258,192] 13 (by decide) (choices 1) [1,64] r32391 c32391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15614
  · exact u15615

def b32392 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 23, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 13 35 22 296 19 224 192 192 448), lower := (rows 13 35 22 296 19 32 64 128 256), losses := [] }

theorem u32392 : Upper (D 7) (R 7) [12,33,18,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32393 : Route 9 := (fun mask => (mask,id))

def c32393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32393 : Upper (D 7) (R 7) [12,33,18,288,65] 13 := by
  apply FastRouting.sound _ _ [12,33,18,288,65] 13 (by decide) (choices 1) [2,64,128] r32393 c32393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15616
  · exact u15617
  · exact u15618

def b32394 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 225 }], pairs := [(2,0),(2,5),(2,6),(2,7)], upper := (rows 13 35 22 296 82 225 193 193 449), lower := (rows 13 35 22 296 82 32 64 128 256), losses := [] }

theorem u32394 : Upper (D 7) (R 7) [12,33,18,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32395 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32395 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32395 : Upper (D 7) (R 7) [12,33,18,288,192] 13 := by
  apply FastRouting.sound _ _ [12,33,18,288,192] 13 (by decide) (choices 1) [1,2,64] r32395 c32395
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u15619
  · exact u15620
  · exact u15621

def b32396 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 20, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(4,5)], upper := (rows 13 35 22 328 19 224 224 224 480), lower := (rows 13 35 22 328 19 32 64 128 256), losses := [] }

theorem u32396 : Upper (D 7) (R 7) [12,33,18,320,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32397 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 20, targets := 192 }], pairs := [(2,6),(2,7),(4,6),(4,7)], upper := (rows 13 35 22 328 49 226 194 194 450), lower := (rows 13 35 22 328 49 32 64 128 256), losses := [] }

theorem u32397 : Upper (D 7) (R 7) [12,33,18,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32398 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 20, targets := 193 }], pairs := [(2,0),(2,6),(2,7),(4,0)], upper := (rows 13 35 22 328 50 225 193 193 449), lower := (rows 13 35 22 328 50 32 64 128 256), losses := [] }

theorem u32398 : Upper (D 7) (R 7) [12,33,18,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32399 : Route 9 := (fun mask => (mask,id))

def c32399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32399 : Upper (D 7) (R 7) [12,33,18,320,65] 13 := by
  apply FastRouting.sound _ _ [12,33,18,320,65] 13 (by decide) (choices 1) [2,128] r32399 c32399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15622
  · exact u15623

#print axioms u32399
end Delivery.IrregularNine14.P07
