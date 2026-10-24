import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0273
import IrregularNine14P06C0274

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33360 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 100 280 22 97 97 225 353), lower := (rows 11 134 100 280 22 32 64 128 256), losses := [] }

theorem u33360 : Upper (D 6) (R 6) [10,132,96,272,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33361 : Route 9 := (fun mask => (mask,id))

def c33361 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33361 : Upper (D 6) (R 6) [10,132,96,272,33] 13 := by
  apply FastRouting.sound _ _ [10,132,96,272,33] 13 (by decide) (choices 1) [1,2,4,64] r33361 c33361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16386
  · exact u16387
  · exact u16388
  · exact u16389

def r33362 : Route 9 := (fun mask => (mask,id))

def c33362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33362 : Upper (D 6) (R 6) [10,132,96,272,34] 13 := by
  apply FastRouting.sound _ _ [10,132,96,272,34] 13 (by decide) (choices 1) [1,4,64] r33362 c33362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16390
  · exact u16391
  · exact u16392

def b33363 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 100 280 52 99 67 195 323), lower := (rows 11 134 100 280 52 32 64 128 256), losses := [] }

theorem u33363 : Upper (D 6) (R 6) [10,132,96,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33364 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 3 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 11 134 100 280 112 39 71 135 263), lower := (rows 11 134 100 280 112 32 64 128 256), losses := [] }

theorem u33364 : Upper (D 6) (R 6) [10,132,96,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33365 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 100 296 19 117 85 213 341), lower := (rows 11 134 100 296 19 32 64 128 256), losses := [] }

theorem u33365 : Upper (D 6) (R 6) [10,132,96,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33366 : Route 9 := (fun mask => (mask,id))

def c33366 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33366 : Upper (D 6) (R 6) [10,132,96,288,5] 13 := by
  apply FastRouting.sound _ _ [10,132,96,288,5] 13 (by decide) (choices 1) [1,2,16,64] r33366 c33366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16393
  · exact u16394
  · exact u16395
  · exact u16396

def b33367 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 100 296 22 113 81 209 337), lower := (rows 11 134 100 296 22 32 64 128 256), losses := [] }

theorem u33367 : Upper (D 6) (R 6) [10,132,96,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33368 : Route 9 := (fun mask => (mask,id))

def c33368 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33368 : Upper (D 6) (R 6) [10,132,96,288,65] 13 := by
  apply FastRouting.sound _ _ [10,132,96,288,65] 13 (by decide) (choices 1) [1,2,4,16] r33368 c33368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16397
  · exact u16398
  · exact u16399
  · exact u16400

def r33369 : Route 9 := (fun mask => (mask,id))

def c33369 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33369 : Upper (D 6) (R 6) [10,132,96,288,66] 13 := by
  apply FastRouting.sound _ _ [10,132,96,288,66] 13 (by decide) (choices 1) [1,4,16] r33369 c33369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16401
  · exact u16402
  · exact u16403

def b33370 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 134 100 296 84 51 83 147 275), lower := (rows 11 134 100 296 84 32 64 128 256), losses := [] }

theorem u33370 : Upper (D 6) (R 6) [10,132,96,288,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33371 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 261 25 22 96 96 224 352), lower := (rows 11 134 261 25 22 32 64 128 256), losses := [] }

theorem u33371 : Upper (D 6) (R 6) [10,132,257,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33372 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 261 25 50 100 100 228 356), lower := (rows 11 134 261 25 50 32 64 128 256), losses := [] }

theorem u33372 : Upper (D 6) (R 6) [10,132,257,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33373 : Route 9 := (fun mask => (mask,id))

def c33373 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33373 : Upper (D 6) (R 6) [10,132,257,17,36] 13 := by
  apply FastRouting.sound _ _ [10,132,257,17,36] 13 (by decide) (choices 1) [2,64] r33373 c33373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16404
  · exact u16405

def r33374 : Route 9 := (fun mask => (mask,id))

def c33374 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33374 : Upper (D 6) (R 6) [10,132,257,17,96] 13 := by
  apply FastRouting.sound _ _ [10,132,257,17,96] 13 (by decide) (choices 1) [2,4,64] r33374 c33374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16406
  · exact u16407
  · exact u16408

def b33375 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 261 28 19 96 96 224 352), lower := (rows 11 134 261 28 19 32 64 128 256), losses := [] }

theorem u33375 : Upper (D 6) (R 6) [10,132,257,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33376 : Route 9 := (fun mask => (mask,id))

def c33376 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33376 : Upper (D 6) (R 6) [10,132,257,20,33] 13 := by
  apply FastRouting.sound _ _ [10,132,257,20,33] 13 (by decide) (choices 1) [2,64] r33376 c33376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16409
  · exact u16410

def r33377 : Route 9 := (fun mask => (mask,id))

def c33377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33377 : Upper (D 6) (R 6) [10,132,257,20,34] 13 := by
  apply FastRouting.sound _ _ [10,132,257,20,34] 13 (by decide) (choices 1) [1,64] r33377 c33377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16411
  · exact u16412

def r33378 : Route 9 := (fun mask => (mask,id))

def c33378 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33378 : Upper (D 6) (R 6) [10,132,257,20,96] 13 := by
  apply FastRouting.sound _ _ [10,132,257,20,96] 13 (by decide) (choices 1) [1,2,64] r33378 c33378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16413
  · exact u16414
  · exact u16415

def b33379 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 16, targets := 96 },{ cop := 2, region := 242, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 11 134 261 41 22 112 112 240 368), lower := (rows 11 134 261 41 22 32 64 128 256), losses := [] }

theorem u33379 : Upper (D 6) (R 6) [10,132,257,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33380 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 261 41 50 116 84 212 340), lower := (rows 11 134 261 41 50 32 64 128 256), losses := [] }

theorem u33380 : Upper (D 6) (R 6) [10,132,257,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33381 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 242, targets := 1 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 11 134 261 41 52 114 82 210 338), lower := (rows 11 134 261 41 52 32 64 128 256), losses := [] }

theorem u33381 : Upper (D 6) (R 6) [10,132,257,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33382 : Route 9 := (fun mask => (mask,id))

def c33382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33382 : Upper (D 6) (R 6) [10,132,257,33,66] 13 := by
  apply FastRouting.sound _ _ [10,132,257,33,66] 13 (by decide) (choices 1) [4,16,64] r33382 c33382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16416
  · exact u16417
  · exact u16418

def r33383 : Route 9 := (fun mask => (mask,id))

def c33383 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33383 : Upper (D 6) (R 6) [10,132,257,33,68] 13 := by
  apply FastRouting.sound _ _ [10,132,257,33,68] 13 (by decide) (choices 1) [2,16,64] r33383 c33383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16419
  · exact u16420
  · exact u16421

def r33384 : Route 9 := (fun mask => (mask,id))

def c33384 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33384 : Upper (D 6) (R 6) [10,132,257,33,96] 13 := by
  apply FastRouting.sound _ _ [10,132,257,33,96] 13 (by decide) (choices 1) [2,4,16,64] r33384 c33384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16422
  · exact u16423
  · exact u16424
  · exact u16425

def b33385 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 134 261 44 19 112 112 240 368), lower := (rows 11 134 261 44 19 32 64 128 256), losses := [] }

theorem u33385 : Upper (D 6) (R 6) [10,132,257,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33386 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 454, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,5),(2,5),(4,2)], upper := (rows 11 134 261 44 49 114 82 210 338), lower := (rows 11 134 261 44 49 32 64 128 256), losses := [] }

theorem u33386 : Upper (D 6) (R 6) [10,132,257,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33387 : Route 9 := (fun mask => (mask,id))

def c33387 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33387 : Upper (D 6) (R 6) [10,132,257,36,34] 13 := by
  apply FastRouting.sound _ _ [10,132,257,36,34] 13 (by decide) (choices 1) [1,16,64] r33387 c33387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16426
  · exact u16427
  · exact u16428

def r33388 : Route 9 := (fun mask => (mask,id))

def c33388 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33388 : Upper (D 6) (R 6) [10,132,257,36,65] 13 := by
  apply FastRouting.sound _ _ [10,132,257,36,65] 13 (by decide) (choices 1) [2,16,64] r33388 c33388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16429
  · exact u16430
  · exact u16431

def r33389 : Route 9 := (fun mask => (mask,id))

def c33389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33389 : Upper (D 6) (R 6) [10,132,257,36,66] 13 := by
  apply FastRouting.sound _ _ [10,132,257,36,66] 13 (by decide) (choices 1) [1,16,64] r33389 c33389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16432
  · exact u16433
  · exact u16434

def r33390 : Route 9 := (fun mask => (mask,id))

def c33390 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33390 : Upper (D 6) (R 6) [10,132,257,36,96] 13 := by
  apply FastRouting.sound _ _ [10,132,257,36,96] 13 (by decide) (choices 1) [1,2,16,64] r33390 c33390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16435
  · exact u16436
  · exact u16437
  · exact u16438

def b33391 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 261 56 19 100 100 228 356), lower := (rows 11 134 261 56 19 32 64 128 256), losses := [] }

theorem u33391 : Upper (D 6) (R 6) [10,132,257,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33392 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 134 261 56 21 98 98 226 354), lower := (rows 11 134 261 56 21 32 64 128 256), losses := [] }

theorem u33392 : Upper (D 6) (R 6) [10,132,257,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33393 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 261 56 22 97 97 225 353), lower := (rows 11 134 261 56 22 32 64 128 256), losses := [] }

theorem u33393 : Upper (D 6) (R 6) [10,132,257,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33394 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 261 56 49 102 70 198 326), lower := (rows 11 134 261 56 49 32 64 128 256), losses := [] }

theorem u33394 : Upper (D 6) (R 6) [10,132,257,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33395 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 261 56 50 101 69 197 325), lower := (rows 11 134 261 56 50 32 64 128 256), losses := [] }

theorem u33395 : Upper (D 6) (R 6) [10,132,257,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33396 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 261 56 52 99 67 195 323), lower := (rows 11 134 261 56 52 32 64 128 256), losses := [] }

theorem u33396 : Upper (D 6) (R 6) [10,132,257,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33397 : Route 9 := (fun mask => (mask,id))

def c33397 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33397 : Upper (D 6) (R 6) [10,132,257,48,65] 13 := by
  apply FastRouting.sound _ _ [10,132,257,48,65] 13 (by decide) (choices 1) [2,4,64] r33397 c33397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16439
  · exact u16440
  · exact u16441

def r33398 : Route 9 := (fun mask => (mask,id))

def c33398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33398 : Upper (D 6) (R 6) [10,132,257,48,66] 13 := by
  apply FastRouting.sound _ _ [10,132,257,48,66] 13 (by decide) (choices 1) [1,4,64] r33398 c33398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16442
  · exact u16443
  · exact u16444

def r33399 : Route 9 := (fun mask => (mask,id))

def c33399 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33399 : Upper (D 6) (R 6) [10,132,257,48,68] 13 := by
  apply FastRouting.sound _ _ [10,132,257,48,68] 13 (by decide) (choices 1) [1,2,64] r33399 c33399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16445
  · exact u16446
  · exact u16447

def b33400 : PairBound 9 := { available := 71, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 261 56 112 103 71 199 327), lower := (rows 11 134 261 56 112 32 64 128 256), losses := [] }

theorem u33400 : Upper (D 6) (R 6) [10,132,257,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33401 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 261 104 19 116 116 244 372), lower := (rows 11 134 261 104 19 32 64 128 256), losses := [] }

theorem u33401 : Upper (D 6) (R 6) [10,132,257,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33401 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33402 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 134 261 104 21 114 114 242 370), lower := (rows 11 134 261 104 21 32 64 128 256), losses := [] }

theorem u33402 : Upper (D 6) (R 6) [10,132,257,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33403 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 261 104 22 113 113 241 369), lower := (rows 11 134 261 104 22 32 64 128 256), losses := [] }

theorem u33403 : Upper (D 6) (R 6) [10,132,257,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33404 : Route 9 := (fun mask => (mask,id))

def c33404 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33404 : Upper (D 6) (R 6) [10,132,257,96,33] 13 := by
  apply FastRouting.sound _ _ [10,132,257,96,33] 13 (by decide) (choices 1) [2,4,16,64] r33404 c33404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16448
  · exact u16449
  · exact u16450
  · exact u16451

def r33405 : Route 9 := (fun mask => (mask,id))

def c33405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33405 : Upper (D 6) (R 6) [10,132,257,96,34] 13 := by
  apply FastRouting.sound _ _ [10,132,257,96,34] 13 (by decide) (choices 1) [1,4,16,64] r33405 c33405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16452
  · exact u16453
  · exact u16454
  · exact u16455

def r33406 : Route 9 := (fun mask => (mask,id))

def c33406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33406 : Upper (D 6) (R 6) [10,132,257,96,36] 13 := by
  apply FastRouting.sound _ _ [10,132,257,96,36] 13 (by decide) (choices 1) [1,2,16,64] r33406 c33406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16456
  · exact u16457
  · exact u16458
  · exact u16459

def b33407 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 134 261 104 112 55 87 151 279), lower := (rows 11 134 261 104 112 32 64 128 256), losses := [] }

theorem u33407 : Upper (D 6) (R 6) [10,132,257,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33408 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 262 25 21 96 96 224 352), lower := (rows 11 134 262 25 21 32 64 128 256), losses := [] }

theorem u33408 : Upper (D 6) (R 6) [10,132,258,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33409 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 134 262 25 49 100 100 228 356), lower := (rows 11 134 262 25 49 32 64 128 256), losses := [] }

theorem u33409 : Upper (D 6) (R 6) [10,132,258,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33410 : Route 9 := (fun mask => (mask,id))

def c33410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33410 : Upper (D 6) (R 6) [10,132,258,17,36] 13 := by
  apply FastRouting.sound _ _ [10,132,258,17,36] 13 (by decide) (choices 1) [1,64] r33410 c33410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16460
  · exact u16461

def r33411 : Route 9 := (fun mask => (mask,id))

def c33411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33411 : Upper (D 6) (R 6) [10,132,258,17,96] 13 := by
  apply FastRouting.sound _ _ [10,132,258,17,96] 13 (by decide) (choices 1) [1,4,64] r33411 c33411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16462
  · exact u16463
  · exact u16464

def r33412 : Route 9 := (fun mask => (mask,id))

def c33412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33412 : Upper (D 6) (R 6) [10,132,258,20,33] 13 := by
  apply FastRouting.sound _ _ [10,132,258,20,33] 13 (by decide) (choices 1) [1,64] r33412 c33412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16465
  · exact u16466

def r33413 : Route 9 := (fun mask => (mask,id))

def c33413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33413 : Upper (D 6) (R 6) [10,132,258,20,96] 13 := by
  apply FastRouting.sound _ _ [10,132,258,20,96] 13 (by decide) (choices 1) [1,64] r33413 c33413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16467
  · exact u16468

def b33414 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 104, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 134 262 41 21 112 112 240 368), lower := (rows 11 134 262 41 21 32 64 128 256), losses := [] }

theorem u33414 : Upper (D 6) (R 6) [10,132,258,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33415 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 134 262 41 49 116 84 212 340), lower := (rows 11 134 262 41 49 32 64 128 256), losses := [] }

theorem u33415 : Upper (D 6) (R 6) [10,132,258,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33416 : Route 9 := (fun mask => (mask,id))

def c33416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33416 : Upper (D 6) (R 6) [10,132,258,33,36] 13 := by
  apply FastRouting.sound _ _ [10,132,258,33,36] 13 (by decide) (choices 1) [1,16,64] r33416 c33416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16469
  · exact u16470
  · exact u16471

def r33417 : Route 9 := (fun mask => (mask,id))

def c33417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33417 : Upper (D 6) (R 6) [10,132,258,33,65] 13 := by
  apply FastRouting.sound _ _ [10,132,258,33,65] 13 (by decide) (choices 1) [4,16,64] r33417 c33417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16472
  · exact u16473
  · exact u16474

def r33418 : Route 9 := (fun mask => (mask,id))

def c33418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33418 : Upper (D 6) (R 6) [10,132,258,33,68] 13 := by
  apply FastRouting.sound _ _ [10,132,258,33,68] 13 (by decide) (choices 1) [1,16,64] r33418 c33418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16475
  · exact u16476
  · exact u16477

def r33419 : Route 9 := (fun mask => (mask,id))

def c33419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33419 : Upper (D 6) (R 6) [10,132,258,33,96] 13 := by
  apply FastRouting.sound _ _ [10,132,258,33,96] 13 (by decide) (choices 1) [1,4,16,64] r33419 c33419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16478
  · exact u16479
  · exact u16480
  · exact u16481

#print axioms u33419
end Delivery.IrregularNine14.P06
