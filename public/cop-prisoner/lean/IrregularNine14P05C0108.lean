import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0049
import IrregularNine14P05C0050

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6480 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 362, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 67 148 296 52 43 75 139 267), lower := (rows 7 67 148 296 52 32 64 128 256), losses := [] }

theorem u6480 : Upper (D 5) (R 5) [6,65,144,288,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6480
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6481 : PairBound 9 := { available := 15, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 148 296 56 47 79 143 271), lower := (rows 7 67 148 296 56 32 64 128 256), losses := [] }

theorem u6481 : Upper (D 5) (R 5) [6,65,144,288,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6481
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6482 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 67 164 25 22 296 360 424 296), lower := (rows 7 67 164 25 22 32 64 128 256), losses := [] }

theorem u6482 : Upper (D 5) (R 5) [6,65,160,17,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6482
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6483 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 67 164 25 26 300 364 428 300), lower := (rows 7 67 164 25 26 32 64 128 256), losses := [] }

theorem u6483 : Upper (D 5) (R 5) [6,65,160,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6483
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6484 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 67 164 25 28 298 362 426 298), lower := (rows 7 67 164 25 28 32 64 128 256), losses := [] }

theorem u6484 : Upper (D 5) (R 5) [6,65,160,17,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6484
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6485 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 25 50 300 332 396 268), lower := (rows 7 67 164 25 50 32 64 128 256), losses := [] }

theorem u6485 : Upper (D 5) (R 5) [6,65,160,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6485
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6486 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 164 25 52 298 330 394 266), lower := (rows 7 67 164 25 52 32 64 128 256), losses := [] }

theorem u6486 : Upper (D 5) (R 5) [6,65,160,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6486
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6487 : Route 9 := (fun mask => (mask,id))

def c6487 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6487 : Upper (D 5) (R 5) [6,65,160,17,40] 13 := by
  apply FastRouting.sound _ _ [6,65,160,17,40] 13 (by decide) (choices 1) [2,4,8,256] r6487 c6487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2940
  · exact u2941
  · exact u2942
  · exact u2943

def b6488 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 25 274 44 108 172 300), lower := (rows 7 67 164 25 274 32 64 128 256), losses := [] }

theorem u6488 : Upper (D 5) (R 5) [6,65,160,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6488
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6489 : Route 9 := (fun mask => (mask,id))

def c6489 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6489 : Upper (D 5) (R 5) [6,65,160,17,260] 13 := by
  apply FastRouting.sound _ _ [6,65,160,17,260] 13 (by decide) (choices 1) [2,8] r6489 c6489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2944
  · exact u2945

def r6490 : Route 9 := (fun mask => (mask,id))

def c6490 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6490 : Upper (D 5) (R 5) [6,65,160,17,264] 13 := by
  apply FastRouting.sound _ _ [6,65,160,17,264] 13 (by decide) (choices 1) [2,4,8] r6490 c6490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2946
  · exact u2947
  · exact u2948

def r6491 : Route 9 := (fun mask => (mask,id))

def c6491 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6491 : Upper (D 5) (R 5) [6,65,160,17,288] 13 := by
  apply FastRouting.sound _ _ [6,65,160,17,288] 13 (by decide) (choices 1) [2,4,8] r6491 c6491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2949
  · exact u2950
  · exact u2951

def b6492 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 164 26 21 296 360 424 296), lower := (rows 7 67 164 26 21 32 64 128 256), losses := [] }

theorem u6492 : Upper (D 5) (R 5) [6,65,160,18,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6492
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6493 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 24, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 67 164 26 25 300 364 428 300), lower := (rows 7 67 164 26 25 32 64 128 256), losses := [] }

theorem u6493 : Upper (D 5) (R 5) [6,65,160,18,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6493
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6494 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 164 26 28 297 361 425 297), lower := (rows 7 67 164 26 28 32 64 128 256), losses := [] }

theorem u6494 : Upper (D 5) (R 5) [6,65,160,18,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6494
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6495 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 26 49 300 332 396 268), lower := (rows 7 67 164 26 49 32 64 128 256), losses := [] }

theorem u6495 : Upper (D 5) (R 5) [6,65,160,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6495
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6496 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 164 26 52 297 329 393 265), lower := (rows 7 67 164 26 52 32 64 128 256), losses := [] }

theorem u6496 : Upper (D 5) (R 5) [6,65,160,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6496
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6497 : Route 9 := (fun mask => (mask,id))

def c6497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6497 : Upper (D 5) (R 5) [6,65,160,18,40] 13 := by
  apply FastRouting.sound _ _ [6,65,160,18,40] 13 (by decide) (choices 1) [1,4,8,256] r6497 c6497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2952
  · exact u2953
  · exact u2954
  · exact u2955

def b6498 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 26 273 44 108 172 300), lower := (rows 7 67 164 26 273 32 64 128 256), losses := [] }

theorem u6498 : Upper (D 5) (R 5) [6,65,160,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6498
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6499 : Route 9 := (fun mask => (mask,id))

def c6499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6499 : Upper (D 5) (R 5) [6,65,160,18,260] 13 := by
  apply FastRouting.sound _ _ [6,65,160,18,260] 13 (by decide) (choices 1) [1,8] r6499 c6499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2956
  · exact u2957

def r6500 : Route 9 := (fun mask => (mask,id))

def c6500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6500 : Upper (D 5) (R 5) [6,65,160,18,264] 13 := by
  apply FastRouting.sound _ _ [6,65,160,18,264] 13 (by decide) (choices 1) [1,4,8] r6500 c6500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2958
  · exact u2959
  · exact u2960

def r6501 : Route 9 := (fun mask => (mask,id))

def c6501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6501 : Upper (D 5) (R 5) [6,65,160,18,288] 13 := by
  apply FastRouting.sound _ _ [6,65,160,18,288] 13 (by decide) (choices 1) [1,4,8] r6501 c6501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2961
  · exact u2962
  · exact u2963

def b6502 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 28 19 296 360 424 296), lower := (rows 7 67 164 28 19 32 64 128 256), losses := [] }

theorem u6502 : Upper (D 5) (R 5) [6,65,160,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6502
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6503 : PairBound 9 := { available := 298, camps := [{ cop := 0, region := 24, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 67 164 28 25 298 362 426 298), lower := (rows 7 67 164 28 25 32 64 128 256), losses := [] }

theorem u6503 : Upper (D 5) (R 5) [6,65,160,20,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6503
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6504 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 24, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 164 28 26 297 361 425 297), lower := (rows 7 67 164 28 26 32 64 128 256), losses := [] }

theorem u6504 : Upper (D 5) (R 5) [6,65,160,20,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6504
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6505 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 28 49 298 330 394 266), lower := (rows 7 67 164 28 49 32 64 128 256), losses := [] }

theorem u6505 : Upper (D 5) (R 5) [6,65,160,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6505
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6506 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 28 50 297 329 393 265), lower := (rows 7 67 164 28 50 32 64 128 256), losses := [] }

theorem u6506 : Upper (D 5) (R 5) [6,65,160,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6506
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6507 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 164 28 56 299 331 395 267), lower := (rows 7 67 164 28 56 32 64 128 256), losses := [] }

theorem u6507 : Upper (D 5) (R 5) [6,65,160,20,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6507
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6508 : Route 9 := (fun mask => (mask,id))

def c6508 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6508 : Upper (D 5) (R 5) [6,65,160,20,257] 13 := by
  apply FastRouting.sound _ _ [6,65,160,20,257] 13 (by decide) (choices 1) [2,8] r6508 c6508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2964
  · exact u2965

def r6509 : Route 9 := (fun mask => (mask,id))

def c6509 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6509 : Upper (D 5) (R 5) [6,65,160,20,258] 13 := by
  apply FastRouting.sound _ _ [6,65,160,20,258] 13 (by decide) (choices 1) [1,8] r6509 c6509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2966
  · exact u2967

def r6510 : Route 9 := (fun mask => (mask,id))

def c6510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6510 : Upper (D 5) (R 5) [6,65,160,20,264] 13 := by
  apply FastRouting.sound _ _ [6,65,160,20,264] 13 (by decide) (choices 1) [1,2,8] r6510 c6510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2968
  · exact u2969
  · exact u2970

def b6511 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 67, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 28 304 43 75 139 267), lower := (rows 7 67 164 28 304 32 64 128 256), losses := [] }

theorem u6511 : Upper (D 5) (R 5) [6,65,160,20,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6511
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6512 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 67 164 41 22 312 344 408 280), lower := (rows 7 67 164 41 22 32 64 128 256), losses := [] }

theorem u6512 : Upper (D 5) (R 5) [6,65,160,33,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6512
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6513 : PairBound 9 := { available := 284, camps := [{ cop := 4, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 41 26 316 348 412 284), lower := (rows 7 67 164 41 26 32 64 128 256), losses := [] }

theorem u6513 : Upper (D 5) (R 5) [6,65,160,33,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6513
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6514 : PairBound 9 := { available := 282, camps := [{ cop := 4, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 41 28 314 346 410 282), lower := (rows 7 67 164 41 28 32 64 128 256), losses := [] }

theorem u6514 : Upper (D 5) (R 5) [6,65,160,33,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6514
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6515 : Route 9 := (fun mask => (mask,id))

def c6515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6515 : Upper (D 5) (R 5) [6,65,160,33,258] 13 := by
  apply FastRouting.sound _ _ [6,65,160,33,258] 13 (by decide) (choices 1) [4,8,16] r6515 c6515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2971
  · exact u2972
  · exact u2973

def r6516 : Route 9 := (fun mask => (mask,id))

def c6516 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6516 : Upper (D 5) (R 5) [6,65,160,33,260] 13 := by
  apply FastRouting.sound _ _ [6,65,160,33,260] 13 (by decide) (choices 1) [2,8,16] r6516 c6516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2974
  · exact u2975
  · exact u2976

def r6517 : Route 9 := (fun mask => (mask,id))

def c6517 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6517 : Upper (D 5) (R 5) [6,65,160,33,264] 13 := by
  apply FastRouting.sound _ _ [6,65,160,33,264] 13 (by decide) (choices 1) [2,4,8,16] r6517 c6517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2977
  · exact u2978
  · exact u2979
  · exact u2980

def b6518 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 164 42 21 312 344 408 280), lower := (rows 7 67 164 42 21 32 64 128 256), losses := [] }

theorem u6518 : Upper (D 5) (R 5) [6,65,160,34,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6518
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6519 : PairBound 9 := { available := 284, camps := [{ cop := 4, region := 420, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 42 25 316 348 412 284), lower := (rows 7 67 164 42 25 32 64 128 256), losses := [] }

theorem u6519 : Upper (D 5) (R 5) [6,65,160,34,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6519
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6520 : PairBound 9 := { available := 281, camps := [{ cop := 4, region := 323, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 67 164 42 28 313 345 409 281), lower := (rows 7 67 164 42 28 32 64 128 256), losses := [] }

theorem u6520 : Upper (D 5) (R 5) [6,65,160,34,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6520
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6521 : Route 9 := (fun mask => (mask,id))

def c6521 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6521 : Upper (D 5) (R 5) [6,65,160,34,257] 13 := by
  apply FastRouting.sound _ _ [6,65,160,34,257] 13 (by decide) (choices 1) [4,8,16] r6521 c6521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2981
  · exact u2982
  · exact u2983

def r6522 : Route 9 := (fun mask => (mask,id))

def c6522 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6522 : Upper (D 5) (R 5) [6,65,160,34,260] 13 := by
  apply FastRouting.sound _ _ [6,65,160,34,260] 13 (by decide) (choices 1) [1,8,16] r6522 c6522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2984
  · exact u2985
  · exact u2986

def r6523 : Route 9 := (fun mask => (mask,id))

def c6523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6523 : Upper (D 5) (R 5) [6,65,160,34,264] 13 := by
  apply FastRouting.sound _ _ [6,65,160,34,264] 13 (by decide) (choices 1) [1,4,8,16] r6523 c6523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2987
  · exact u2988
  · exact u2989
  · exact u2990

def b6524 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 56 19 300 332 396 268), lower := (rows 7 67 164 56 19 32 64 128 256), losses := [] }

theorem u6524 : Upper (D 5) (R 5) [6,65,160,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6524
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6525 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 164 56 21 298 330 394 266), lower := (rows 7 67 164 56 21 32 64 128 256), losses := [] }

theorem u6525 : Upper (D 5) (R 5) [6,65,160,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6525
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6526 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 67 164 56 22 297 329 393 265), lower := (rows 7 67 164 56 22 32 64 128 256), losses := [] }

theorem u6526 : Upper (D 5) (R 5) [6,65,160,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6526
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6527 : Route 9 := (fun mask => (mask,id))

def c6527 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6527 : Upper (D 5) (R 5) [6,65,160,48,9] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,9] 13 (by decide) (choices 1) [2,4,8,256] r6527 c6527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2991
  · exact u2992
  · exact u2993
  · exact u2994

def r6528 : Route 9 := (fun mask => (mask,id))

def c6528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6528 : Upper (D 5) (R 5) [6,65,160,48,10] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,10] 13 (by decide) (choices 1) [1,4,8,256] r6528 c6528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2995
  · exact u2996
  · exact u2997
  · exact u2998

def b6529 : PairBound 9 := { available := 267, camps := [{ cop := 2, region := 24, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 67 164 56 28 299 331 395 267), lower := (rows 7 67 164 56 28 32 64 128 256), losses := [] }

theorem u6529 : Upper (D 5) (R 5) [6,65,160,48,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6529
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6530 : Route 9 := (fun mask => (mask,id))

def c6530 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6530 : Upper (D 5) (R 5) [6,65,160,48,257] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,257] 13 (by decide) (choices 1) [2,4,8] r6530 c6530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2999
  · exact u3000
  · exact u3001

def r6531 : Route 9 := (fun mask => (mask,id))

def c6531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6531 : Upper (D 5) (R 5) [6,65,160,48,258] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,258] 13 (by decide) (choices 1) [1,4,8] r6531 c6531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3002
  · exact u3003
  · exact u3004

def r6532 : Route 9 := (fun mask => (mask,id))

def c6532 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6532 : Upper (D 5) (R 5) [6,65,160,48,260] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,260] 13 (by decide) (choices 1) [1,2,8] r6532 c6532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3005
  · exact u3006
  · exact u3007

def r6533 : Route 9 := (fun mask => (mask,id))

def c6533 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6533 : Upper (D 5) (R 5) [6,65,160,48,264] 13 := by
  apply FastRouting.sound _ _ [6,65,160,48,264] 13 (by decide) (choices 1) [1,2,4,8] r6533 c6533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3008
  · exact u3009
  · exact u3010
  · exact u3011

def b6534 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 67 164 265 22 56 120 184 312), lower := (rows 7 67 164 265 22 32 64 128 256), losses := [] }

theorem u6534 : Upper (D 5) (R 5) [6,65,160,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6534
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6535 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 164, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 164 265 26 60 124 188 316), lower := (rows 7 67 164 265 26 32 64 128 256), losses := [] }

theorem u6535 : Upper (D 5) (R 5) [6,65,160,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6535
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6536 : Route 9 := (fun mask => (mask,id))

def c6536 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6536 : Upper (D 5) (R 5) [6,65,160,257,12] 13 := by
  apply FastRouting.sound _ _ [6,65,160,257,12] 13 (by decide) (choices 1) [2,8,16] r6536 c6536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3012
  · exact u3013
  · exact u3014

def r6537 : Route 9 := (fun mask => (mask,id))

def c6537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6537 : Upper (D 5) (R 5) [6,65,160,257,34] 13 := by
  apply FastRouting.sound _ _ [6,65,160,257,34] 13 (by decide) (choices 1) [4,8,16] r6537 c6537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3015
  · exact u3016
  · exact u3017

def b6538 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 67 164 265 52 58 90 154 282), lower := (rows 7 67 164 265 52 32 64 128 256), losses := [] }

theorem u6538 : Upper (D 5) (R 5) [6,65,160,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6538
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6539 : Route 9 := (fun mask => (mask,id))

def c6539 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6539 : Upper (D 5) (R 5) [6,65,160,257,40] 13 := by
  apply FastRouting.sound _ _ [6,65,160,257,40] 13 (by decide) (choices 1) [2,4,8,16] r6539 c6539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3018
  · exact u3019
  · exact u3020
  · exact u3021

#print axioms u6539
end Delivery.IrregularNine14.P05
