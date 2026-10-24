import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0456
import IrregularNine14P06C0457

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b40380 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 131 292 26 81 46 78 142 270), lower := (rows 97 131 292 26 81 32 64 128 256), losses := [] }

theorem u40380 : Upper (D 6) (R 6) [96,129,288,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40381 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 131 292 26 82 45 77 141 269), lower := (rows 97 131 292 26 82 32 64 128 256), losses := [] }

theorem u40381 : Upper (D 6) (R 6) [96,129,288,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40382 : Route 9 := (fun mask => (mask,id))

def c40382 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40382 : Upper (D 6) (R 6) [96,129,288,18,68] 13 := by
  apply FastRouting.sound _ _ [96,129,288,18,68] 13 (by decide) (choices 1) [1,2,4,8] r40382 c40382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27366
  · exact u27367
  · exact u27368
  · exact u27369

def r40383 : Route 9 := (fun mask => (mask,id))

def c40383 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40383 : Upper (D 6) (R 6) [96,129,288,18,72] 13 := by
  apply FastRouting.sound _ _ [96,129,288,18,72] 13 (by decide) (choices 1) [1,2,4] r40383 c40383
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27370
  · exact u27371
  · exact u27372

def b40384 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 97 131 292 28 28 99 67 195 323), lower := (rows 97 131 292 28 28 32 64 128 256), losses := [] }

theorem u40384 : Upper (D 6) (R 6) [96,129,288,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40385 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 131 292 28 81 46 78 142 270), lower := (rows 97 131 292 28 81 32 64 128 256), losses := [] }

theorem u40385 : Upper (D 6) (R 6) [96,129,288,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40386 : Route 9 := (fun mask => (mask,id))

def c40386 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40386 : Upper (D 6) (R 6) [96,129,288,20,66] 13 := by
  apply FastRouting.sound _ _ [96,129,288,20,66] 13 (by decide) (choices 1) [1,2,4,8] r40386 c40386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27373
  · exact u27374
  · exact u27375
  · exact u27376

def b40387 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 97 131 292 28 84 43 75 139 267), lower := (rows 97 131 292 28 84 32 64 128 256), losses := [] }

theorem u40387 : Upper (D 6) (R 6) [96,129,288,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40388 : Route 9 := (fun mask => (mask,id))

def c40388 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40388 : Upper (D 6) (R 6) [96,129,288,20,72] 13 := by
  apply FastRouting.sound _ _ [96,129,288,20,72] 13 (by decide) (choices 1) [1,2,4] r40388 c40388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27377
  · exact u27378
  · exact u27379

theorem m40389_16 : Upper (D 6) (R 6) [96,132,258,3,5,16] 13 :=
  permutation_upper _ _ _ [96,132,258,3,5,8] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27380

def r40389 : Route 9 := (fun mask => (mask,id))

def c40389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40389 : Upper (D 6) (R 6) [96,132,258,3,5] 13 := by
  apply FastRouting.sound _ _ [96,132,258,3,5] 13 (by decide) (choices 1) [8,16,64] r40389 c40389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27380
  · exact m40389_16
  · exact u27381

def b40390 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 134 262 11 25 116 116 244 372), lower := (rows 97 134 262 11 25 32 64 128 256), losses := [] }

theorem u40390 : Upper (D 6) (R 6) [96,132,258,3,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40391 : Route 9 := (fun mask => (mask,id))

def c40391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40391 : Upper (D 6) (R 6) [96,132,258,3,12] 13 := by
  apply FastRouting.sound _ _ [96,132,258,3,12] 13 (by decide) (choices 1) [1,16,64] r40391 c40391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27382
  · exact u27383
  · exact u27384

def b40392 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 134 262 11 49 124 92 220 348), lower := (rows 97 134 262 11 49 32 64 128 256), losses := [] }

theorem u40392 : Upper (D 6) (R 6) [96,132,258,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40393 : Route 9 := (fun mask => (mask,id))

def c40393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40393 : Upper (D 6) (R 6) [96,132,258,3,36] 13 := by
  apply FastRouting.sound _ _ [96,132,258,3,36] 13 (by decide) (choices 1) [1,8,16,64] r40393 c40393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27385
  · exact u27386
  · exact u27387
  · exact u27388

def r40394 : Route 9 := (fun mask => (mask,id))

def c40394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40394 : Upper (D 6) (R 6) [96,132,258,3,40] 13 := by
  apply FastRouting.sound _ _ [96,132,258,3,40] 13 (by decide) (choices 1) [1,4,16,64] r40394 c40394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27389
  · exact u27390
  · exact u27391
  · exact u27392

def b40395 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 134 262 11 112 61 93 157 285), lower := (rows 97 134 262 11 112 32 64 128 256), losses := [] }

theorem u40395 : Upper (D 6) (R 6) [96,132,258,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40396 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 97 134 262 14 25 113 113 241 369), lower := (rows 97 134 262 14 25 32 64 128 256), losses := [] }

theorem u40396 : Upper (D 6) (R 6) [96,132,258,6,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40397 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 97 134 262 14 56 113 81 209 337), lower := (rows 97 134 262 14 56 32 64 128 256), losses := [] }

theorem u40397 : Upper (D 6) (R 6) [96,132,258,6,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40398 : PairBound 9 := { available := 102, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 134 262 25 25 102 102 230 358), lower := (rows 97 134 262 25 25 32 64 128 256), losses := [] }

theorem u40398 : Upper (D 6) (R 6) [96,132,258,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40399 : Route 9 := (fun mask => (mask,id))

def c40399 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40399 : Upper (D 6) (R 6) [96,132,258,17,10] 13 := by
  apply FastRouting.sound _ _ [96,132,258,17,10] 13 (by decide) (choices 1) [1,4,64] r40399 c40399
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27393
  · exact u27394
  · exact u27395

def b40400 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 134 262 25 49 110 78 206 334), lower := (rows 97 134 262 25 49 32 64 128 256), losses := [] }

theorem u40400 : Upper (D 6) (R 6) [96,132,258,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40401 : Route 9 := (fun mask => (mask,id))

def c40401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40401 : Upper (D 6) (R 6) [96,132,258,17,34] 13 := by
  apply FastRouting.sound _ _ [96,132,258,17,34] 13 (by decide) (choices 1) [1,4,8,64] r40401 c40401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27396
  · exact u27397
  · exact u27398
  · exact u27399

def b40402 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 134 262 25 56 103 71 199 327), lower := (rows 97 134 262 25 56 32 64 128 256), losses := [] }

theorem u40402 : Upper (D 6) (R 6) [96,132,258,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40403 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 97 134 262 25 112 47 79 143 271), lower := (rows 97 134 262 25 112 32 64 128 256), losses := [] }

theorem u40403 : Upper (D 6) (R 6) [96,132,258,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40404 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 134 262 26 28 97 97 225 353), lower := (rows 97 134 262 26 28 32 64 128 256), losses := [] }

theorem u40404 : Upper (D 6) (R 6) [96,132,258,18,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40405 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 134 262 26 49 109 77 205 333), lower := (rows 97 134 262 26 49 32 64 128 256), losses := [] }

theorem u40405 : Upper (D 6) (R 6) [96,132,258,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40406 : Route 9 := (fun mask => (mask,id))

def c40406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40406 : Upper (D 6) (R 6) [96,132,258,18,36] 13 := by
  apply FastRouting.sound _ _ [96,132,258,18,36] 13 (by decide) (choices 1) [1,8,64] r40406 c40406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27400
  · exact u27401
  · exact u27402

def b40407 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 1, region := 97, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 97 134 262 26 56 101 69 197 325), lower := (rows 97 134 262 26 56 32 64 128 256), losses := [] }

theorem u40407 : Upper (D 6) (R 6) [96,132,258,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40408 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 134 262 26 112 45 77 141 269), lower := (rows 97 134 262 26 112 32 64 128 256), losses := [] }

theorem u40408 : Upper (D 6) (R 6) [96,132,258,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40409 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 134 262 41 82 61 93 157 285), lower := (rows 97 134 262 41 82 32 64 128 256), losses := [] }

theorem u40409 : Upper (D 6) (R 6) [96,132,258,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40410 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 97 134 262 41 88 55 87 151 279), lower := (rows 97 134 262 41 88 32 64 128 256), losses := [] }

theorem u40410 : Upper (D 6) (R 6) [96,132,258,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40411 : Route 9 := (fun mask => (mask,id))

def c40411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40411 : Upper (D 6) (R 6) [96,132,258,34,68] 13 := by
  apply FastRouting.sound _ _ [96,132,258,34,68] 13 (by decide) (choices 1) [1,8,16] r40411 c40411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27403
  · exact u27404
  · exact u27405

def r40412 : Route 9 := (fun mask => (mask,id))

def c40412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40412 : Upper (D 6) (R 6) [96,132,258,34,72] 13 := by
  apply FastRouting.sound _ _ [96,132,258,34,72] 13 (by decide) (choices 1) [1,4,16] r40412 c40412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27406
  · exact u27407
  · exact u27408

def b40413 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 97 134 262 56 88 39 71 135 263), lower := (rows 97 134 262 56 88 32 64 128 256), losses := [] }

theorem u40413 : Upper (D 6) (R 6) [96,132,258,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40414 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 97 134 268 11 19 116 116 244 372), lower := (rows 97 134 268 11 19 32 64 128 256), losses := [] }

theorem u40414 : Upper (D 6) (R 6) [96,132,264,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40415 : Route 9 := (fun mask => (mask,id))

def c40415 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40415 : Upper (D 6) (R 6) [96,132,264,3,5] 13 := by
  apply FastRouting.sound _ _ [96,132,264,3,5] 13 (by decide) (choices 1) [2,16,64] r40415 c40415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27409
  · exact u27410
  · exact u27411

def b40416 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 97 134 268 11 22 113 113 241 369), lower := (rows 97 134 268 11 22 32 64 128 256), losses := [] }

theorem u40416 : Upper (D 6) (R 6) [96,132,264,3,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40417 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 134 268 11 49 118 86 214 342), lower := (rows 97 134 268 11 49 32 64 128 256), losses := [] }

theorem u40417 : Upper (D 6) (R 6) [96,132,264,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40418 : Route 9 := (fun mask => (mask,id))

def c40418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40418 : Upper (D 6) (R 6) [96,132,264,3,34] 13 := by
  apply FastRouting.sound _ _ [96,132,264,3,34] 13 (by decide) (choices 1) [1,4,16,64] r40418 c40418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27412
  · exact u27413
  · exact u27414
  · exact u27415

def r40419 : Route 9 := (fun mask => (mask,id))

def c40419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40419 : Upper (D 6) (R 6) [96,132,264,3,36] 13 := by
  apply FastRouting.sound _ _ [96,132,264,3,36] 13 (by decide) (choices 1) [1,2,16,64] r40419 c40419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27416
  · exact u27417
  · exact u27418
  · exact u27419

def b40420 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 134 268 11 112 55 87 151 279), lower := (rows 97 134 268 11 112 32 64 128 256), losses := [] }

theorem u40420 : Upper (D 6) (R 6) [96,132,264,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40421 : Route 9 := (fun mask => (mask,id))

def c40421 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40421 : Upper (D 6) (R 6) [96,132,264,5,3] 13 := by
  apply FastRouting.sound _ _ [96,132,264,5,3] 13 (by decide) (choices 1) [2,16,64] r40421 c40421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27420
  · exact u27421
  · exact u27422

def b40422 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 134 268 13 49 114 82 210 338), lower := (rows 97 134 268 13 49 32 64 128 256), losses := [] }

theorem u40422 : Upper (D 6) (R 6) [96,132,264,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40423 : Route 9 := (fun mask => (mask,id))

def c40423 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40423 : Upper (D 6) (R 6) [96,132,264,5,34] 13 := by
  apply FastRouting.sound _ _ [96,132,264,5,34] 13 (by decide) (choices 1) [1,2,16,64] r40423 c40423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27423
  · exact u27424
  · exact u27425
  · exact u27426

def b40424 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 134 268 13 112 51 83 147 275), lower := (rows 97 134 268 13 112 32 64 128 256), losses := [] }

theorem u40424 : Upper (D 6) (R 6) [96,132,264,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40425 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 134 268 25 19 102 102 230 358), lower := (rows 97 134 268 25 19 32 64 128 256), losses := [] }

theorem u40425 : Upper (D 6) (R 6) [96,132,264,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40426 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 134 268 25 21 98 98 226 354), lower := (rows 97 134 268 25 21 32 64 128 256), losses := [] }

theorem u40426 : Upper (D 6) (R 6) [96,132,264,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40427 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 97 134 268 25 22 99 99 227 355), lower := (rows 97 134 268 25 22 32 64 128 256), losses := [] }

theorem u40427 : Upper (D 6) (R 6) [96,132,264,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40428 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 134 268 25 49 102 70 198 326), lower := (rows 97 134 268 25 49 32 64 128 256), losses := [] }

theorem u40428 : Upper (D 6) (R 6) [96,132,264,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40429 : Route 9 := (fun mask => (mask,id))

def c40429 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40429 : Upper (D 6) (R 6) [96,132,264,17,34] 13 := by
  apply FastRouting.sound _ _ [96,132,264,17,34] 13 (by decide) (choices 1) [1,2,4,64] r40429 c40429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27427
  · exact u27428
  · exact u27429
  · exact u27430

def b40430 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 97 134 268 25 52 99 67 195 323), lower := (rows 97 134 268 25 52 32 64 128 256), losses := [] }

theorem u40430 : Upper (D 6) (R 6) [96,132,264,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40431 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 24, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 97 134 268 25 112 39 71 135 263), lower := (rows 97 134 268 25 112 32 64 128 256), losses := [] }

theorem u40431 : Upper (D 6) (R 6) [96,132,264,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40432 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 134 268 26 19 101 101 229 357), lower := (rows 97 134 268 26 19 32 64 128 256), losses := [] }

theorem u40432 : Upper (D 6) (R 6) [96,132,264,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40433 : Route 9 := (fun mask => (mask,id))

def c40433 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40433 : Upper (D 6) (R 6) [96,132,264,18,5] 13 := by
  apply FastRouting.sound _ _ [96,132,264,18,5] 13 (by decide) (choices 1) [1,2,64] r40433 c40433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27431
  · exact u27432
  · exact u27433

def b40434 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 24, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 134 268 26 22 97 97 225 353), lower := (rows 97 134 268 26 22 32 64 128 256), losses := [] }

theorem u40434 : Upper (D 6) (R 6) [96,132,264,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40435 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 134 268 26 49 103 71 199 327), lower := (rows 97 134 268 26 49 32 64 128 256), losses := [] }

theorem u40435 : Upper (D 6) (R 6) [96,132,264,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40436 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 134 268 26 50 101 69 197 325), lower := (rows 97 134 268 26 50 32 64 128 256), losses := [] }

theorem u40436 : Upper (D 6) (R 6) [96,132,264,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40437 : Route 9 := (fun mask => (mask,id))

def c40437 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40437 : Upper (D 6) (R 6) [96,132,264,18,36] 13 := by
  apply FastRouting.sound _ _ [96,132,264,18,36] 13 (by decide) (choices 1) [1,2,64] r40437 c40437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27434
  · exact u27435
  · exact u27436

def b40438 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 134 268 26 112 39 71 135 263), lower := (rows 97 134 268 26 112 32 64 128 256), losses := [] }

theorem u40438 : Upper (D 6) (R 6) [96,132,264,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40439 : Route 9 := (fun mask => (mask,id))

def c40439 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40439 : Upper (D 6) (R 6) [96,132,264,20,3] 13 := by
  apply FastRouting.sound _ _ [96,132,264,20,3] 13 (by decide) (choices 1) [1,2,64] r40439 c40439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27437
  · exact u27438
  · exact u27439

#print axioms u40439
end Delivery.IrregularNine14.P06
