import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0016
import IrregularNine14P05C0017

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3420 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 82 164 265 56 40 71 135 263), lower := (rows 7 82 164 265 56 40 64 128 256), losses := [] }

theorem u3420 : Upper (D 5) (R 5) [6,80,160,257,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3420
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3421 : Route 9 := (fun mask => (mask,id))

def c3421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3421 : Upper (D 5) (R 5) [6,80,160,258,9,1] 13 := by
  apply FastRouting.sound _ _ [6,80,160,258,9,1] 13 (by decide) (choices 1) [4,8,32] r3421 c3421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1003
  · exact u1004
  · exact u1005

def b3422 : PairBound 9 := { available := 41, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 266 25 36 105 169 297), lower := (rows 7 82 164 266 25 36 64 128 256), losses := [] }

theorem u3422 : Upper (D 5) (R 5) [6,80,160,258,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3422
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3423 : Route 9 := (fun mask => (mask,id))

def c3423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3423 : Upper (D 5) (R 5) [6,80,160,258,9,8] 13 := by
  apply FastRouting.sound _ _ [6,80,160,258,9,8] 13 (by decide) (choices 1) [1,4,32] r3423 c3423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1006
  · exact u1007
  · exact u1008

def r3424 : Route 9 := (fun mask => (mask,id))

def c3424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3424 : Upper (D 5) (R 5) [6,80,160,258,12,1] 13 := by
  apply FastRouting.sound _ _ [6,80,160,258,12,1] 13 (by decide) (choices 1) [1,8,32] r3424 c3424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1009
  · exact u1010
  · exact u1011

def r3425 : Route 9 := (fun mask => (mask,id))

def c3425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3425 : Upper (D 5) (R 5) [6,80,160,258,12,8] 13 := by
  apply FastRouting.sound _ _ [6,80,160,258,12,8] 13 (by decide) (choices 1) [1,32] r3425 c3425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1012
  · exact u1013

def r3426 : Route 9 := (fun mask => (mask,id))

def c3426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3426 : Upper (D 5) (R 5) [6,80,160,258,40,1] 13 := by
  apply FastRouting.sound _ _ [6,80,160,258,40,1] 13 (by decide) (choices 1) [1,4,8] r3426 c3426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1014
  · exact u1015
  · exact u1016

def b3427 : PairBound 9 := { available := 9, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 266 56 36 73 137 265), lower := (rows 7 82 164 266 56 36 64 128 256), losses := [] }

theorem u3427 : Upper (D 5) (R 5) [6,80,160,258,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3427
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3428 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 82 164 266 56 40 69 133 261), lower := (rows 7 82 164 266 56 40 64 128 256), losses := [] }

theorem u3428 : Upper (D 5) (R 5) [6,80,160,258,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3428
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3429 : Route 9 := (fun mask => (mask,id))

def c3429 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3429 : Upper (D 5) (R 5) [6,80,160,260,9,1] 13 := by
  apply FastRouting.sound _ _ [6,80,160,260,9,1] 13 (by decide) (choices 1) [2,8,32] r3429 c3429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1017
  · exact u1018
  · exact u1019

def r3430 : Route 9 := (fun mask => (mask,id))

def c3430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3430 : Upper (D 5) (R 5) [6,80,160,260,9,2] 13 := by
  apply FastRouting.sound _ _ [6,80,160,260,9,2] 13 (by decide) (choices 1) [1,8,32] r3430 c3430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1020
  · exact u1021
  · exact u1022

def r3431 : Route 9 := (fun mask => (mask,id))

def c3431 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3431 : Upper (D 5) (R 5) [6,80,160,260,9,8] 13 := by
  apply FastRouting.sound _ _ [6,80,160,260,9,8] 13 (by decide) (choices 1) [1,2,32] r3431 c3431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1023
  · exact u1024
  · exact u1025

def r3432 : Route 9 := (fun mask => (mask,id))

def c3432 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3432 : Upper (D 5) (R 5) [6,80,160,260,40,1] 13 := by
  apply FastRouting.sound _ _ [6,80,160,260,40,1] 13 (by decide) (choices 1) [1,2,8] r3432 c3432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1026
  · exact u1027
  · exact u1028

def b3433 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 264, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 82 164 268 56 34 73 137 265), lower := (rows 7 82 164 268 56 34 64 128 256), losses := [] }

theorem u3433 : Upper (D 5) (R 5) [6,80,160,260,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3433
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3434 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 82 164 268 56 40 67 131 259), lower := (rows 7 82 164 268 56 40 64 128 256), losses := [] }

theorem u3434 : Upper (D 5) (R 5) [6,80,160,260,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3434
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3435 : Route 9 := (fun mask => (mask,id))

def c3435 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3435 : Upper (D 5) (R 5) [6,80,160,288,9,1] 13 := by
  apply FastRouting.sound _ _ [6,80,160,288,9,1] 13 (by decide) (choices 1) [2,4,8] r3435 c3435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1029
  · exact u1030
  · exact u1031

def r3436 : Route 9 := (fun mask => (mask,id))

def c3436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3436 : Upper (D 5) (R 5) [6,80,160,288,9,2] 13 := by
  apply FastRouting.sound _ _ [6,80,160,288,9,2] 13 (by decide) (choices 1) [1,4,8] r3436 c3436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1032
  · exact u1033
  · exact u1034

def b3437 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 82 164 296 25 36 75 139 267), lower := (rows 7 82 164 296 25 36 64 128 256), losses := [] }

theorem u3437 : Upper (D 5) (R 5) [6,80,160,288,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3437
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3438 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 82 164 296 25 40 71 135 263), lower := (rows 7 82 164 296 25 40 64 128 256), losses := [] }

theorem u3438 : Upper (D 5) (R 5) [6,80,160,288,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3438
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3439 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 82 388 41 28 33 106 170 298), lower := (rows 7 82 388 41 28 33 64 128 256), losses := [] }

theorem u3439 : Upper (D 5) (R 5) [6,80,384,33,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3439
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3440 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 82 388 41 28 34 105 169 297), lower := (rows 7 82 388 41 28 34 64 128 256), losses := [] }

theorem u3440 : Upper (D 5) (R 5) [6,80,384,33,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3440
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3441 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 82 388 41 28 40 99 163 291), lower := (rows 7 82 388 41 28 40 64 128 256), losses := [] }

theorem u3441 : Upper (D 5) (R 5) [6,80,384,33,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3441
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3442 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 82 388 41 52 33 74 138 266), lower := (rows 7 82 388 41 52 33 64 128 256), losses := [] }

theorem u3442 : Upper (D 5) (R 5) [6,80,384,33,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3442
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3443 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 404, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 82 388 41 52 34 73 137 265), lower := (rows 7 82 388 41 52 34 64 128 256), losses := [] }

theorem u3443 : Upper (D 5) (R 5) [6,80,384,33,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3443
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3444 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 82 388 41 52 40 75 139 267), lower := (rows 7 82 388 41 52 40 64 128 256), losses := [] }

theorem u3444 : Upper (D 5) (R 5) [6,80,384,33,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3444
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3445 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 82 388 42 25 33 108 172 300), lower := (rows 7 82 388 42 25 33 64 128 256), losses := [] }

theorem u3445 : Upper (D 5) (R 5) [6,80,384,34,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3445
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3446 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 40, targets := 1 },{ cop := 4, region := 420, targets := 2 }], pairs := [(2,1),(3,0)], upper := (rows 7 82 388 42 25 36 105 169 297), lower := (rows 7 82 388 42 25 36 64 128 256), losses := [] }

theorem u3446 : Upper (D 5) (R 5) [6,80,384,34,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3446
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3447 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 82 388 42 25 40 101 165 293), lower := (rows 7 82 388 42 25 40 64 128 256), losses := [] }

theorem u3447 : Upper (D 5) (R 5) [6,80,384,34,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3447
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3448 : Route 9 := (fun mask => (mask,id))

def c3448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3448 : Upper (D 5) (R 5) [6,80,384,34,12,1] 13 := by
  apply FastRouting.sound _ _ [6,80,384,34,12,1] 13 (by decide) (choices 1) [1,8,32] r3448 c3448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1035
  · exact u1036
  · exact u1037

def b3449 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 82 388 42 28 40 97 161 289), lower := (rows 7 82 388 42 28 40 64 128 256), losses := [] }

theorem u3449 : Upper (D 5) (R 5) [6,80,384,34,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3449
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3450 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 82 388 44 25 33 106 170 298), lower := (rows 7 82 388 44 25 33 64 128 256), losses := [] }

theorem u3450 : Upper (D 5) (R 5) [6,80,384,36,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3450
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3451 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 40, targets := 1 },{ cop := 4, region := 98, targets := 4 }], pairs := [(1,2),(3,0)], upper := (rows 7 82 388 44 25 34 105 169 297), lower := (rows 7 82 388 44 25 34 64 128 256), losses := [] }

theorem u3451 : Upper (D 5) (R 5) [6,80,384,36,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3451
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3452 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 82 388 44 25 40 99 163 291), lower := (rows 7 82 388 44 25 40 64 128 256), losses := [] }

theorem u3452 : Upper (D 5) (R 5) [6,80,384,36,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3452
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3453 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 82 388 44 49 33 74 138 266), lower := (rows 7 82 388 44 49 33 64 128 256), losses := [] }

theorem u3453 : Upper (D 5) (R 5) [6,80,384,36,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3453
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3454 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 48, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 82 388 44 49 34 73 137 265), lower := (rows 7 82 388 44 49 34 64 128 256), losses := [] }

theorem u3454 : Upper (D 5) (R 5) [6,80,384,36,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3454
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3455 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 82 388 44 49 40 75 139 267), lower := (rows 7 82 388 44 49 40 64 128 256), losses := [] }

theorem u3455 : Upper (D 5) (R 5) [6,80,384,36,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3455
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3456 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 98 388 25 52 33 74 138 266), lower := (rows 7 98 388 25 52 33 64 128 256), losses := [] }

theorem u3456 : Upper (D 5) (R 5) [6,96,384,17,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3456
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3457 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 388 25 52 34 73 137 265), lower := (rows 7 98 388 25 52 34 64 128 256), losses := [] }

theorem u3457 : Upper (D 5) (R 5) [6,96,384,17,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3457
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3458 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 98 388 25 52 40 75 139 267), lower := (rows 7 98 388 25 52 40 64 128 256), losses := [] }

theorem u3458 : Upper (D 5) (R 5) [6,96,384,17,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3458
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3459 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 56, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 388 25 56 33 78 142 270), lower := (rows 7 98 388 25 56 33 64 128 256), losses := [] }

theorem u3459 : Upper (D 5) (R 5) [6,96,384,17,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3459
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3460 : PairBound 9 := { available := 13, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 388 25 56 34 77 141 269), lower := (rows 7 98 388 25 56 34 64 128 256), losses := [] }

theorem u3460 : Upper (D 5) (R 5) [6,96,384,17,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3460
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3461 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 98 388 25 56 36 75 139 267), lower := (rows 7 98 388 25 56 36 64 128 256), losses := [] }

theorem u3461 : Upper (D 5) (R 5) [6,96,384,17,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3461
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3462 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 56, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 388 25 56 40 71 135 263), lower := (rows 7 98 388 25 56 40 64 128 256), losses := [] }

theorem u3462 : Upper (D 5) (R 5) [6,96,384,17,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3462
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3463 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 98 388 28 49 33 74 138 266), lower := (rows 7 98 388 28 49 33 64 128 256), losses := [] }

theorem u3463 : Upper (D 5) (R 5) [6,96,384,20,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3463
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3464 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 396, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 98 388 28 49 34 73 137 265), lower := (rows 7 98 388 28 49 34 64 128 256), losses := [] }

theorem u3464 : Upper (D 5) (R 5) [6,96,384,20,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3464
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3465 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 98 388 28 49 40 75 139 267), lower := (rows 7 98 388 28 49 40 64 128 256), losses := [] }

theorem u3465 : Upper (D 5) (R 5) [6,96,384,20,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3465
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3466 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 98 388 28 56 33 75 139 267), lower := (rows 7 98 388 28 56 33 64 128 256), losses := [] }

theorem u3466 : Upper (D 5) (R 5) [6,96,384,20,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3466
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3467 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 388 28 56 34 73 137 265), lower := (rows 7 98 388 28 56 34 64 128 256), losses := [] }

theorem u3467 : Upper (D 5) (R 5) [6,96,384,20,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3467
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3468 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 389, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 98 388 28 56 40 67 131 259), lower := (rows 7 98 388 28 56 40 64 128 256), losses := [] }

theorem u3468 : Upper (D 5) (R 5) [6,96,384,20,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3468
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3469 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 98 388 41 28 33 90 154 282), lower := (rows 7 98 388 41 28 33 64 128 256), losses := [] }

theorem u3469 : Upper (D 5) (R 5) [6,96,384,33,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3469
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3470 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 404, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 98 388 41 28 34 89 153 281), lower := (rows 7 98 388 41 28 34 64 128 256), losses := [] }

theorem u3470 : Upper (D 5) (R 5) [6,96,384,33,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3470
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3471 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 98 388 41 28 40 83 147 275), lower := (rows 7 98 388 41 28 40 64 128 256), losses := [] }

theorem u3471 : Upper (D 5) (R 5) [6,96,384,33,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3471
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3472 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1)], upper := (rows 7 98 388 41 28 48 75 139 267), lower := (rows 7 98 388 41 28 48 64 128 256), losses := [] }

theorem u3472 : Upper (D 5) (R 5) [6,96,384,33,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3472
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3473 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 98 388 44 25 33 90 154 282), lower := (rows 7 98 388 44 25 33 64 128 256), losses := [] }

theorem u3473 : Upper (D 5) (R 5) [6,96,384,36,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3473
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3474 : PairBound 9 := { available := 25, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 388 44 25 34 89 153 281), lower := (rows 7 98 388 44 25 34 64 128 256), losses := [] }

theorem u3474 : Upper (D 5) (R 5) [6,96,384,36,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3474
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3475 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 98 388 44 25 40 83 147 275), lower := (rows 7 98 388 44 25 40 64 128 256), losses := [] }

theorem u3475 : Upper (D 5) (R 5) [6,96,384,36,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3475
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3476 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1)], upper := (rows 7 98 388 44 25 48 75 139 267), lower := (rows 7 98 388 44 25 48 64 128 256), losses := [] }

theorem u3476 : Upper (D 5) (R 5) [6,96,384,36,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3476
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3477 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 56, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 388 56 25 33 78 142 270), lower := (rows 7 98 388 56 25 33 64 128 256), losses := [] }

theorem u3477 : Upper (D 5) (R 5) [6,96,384,48,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3477
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3478 : PairBound 9 := { available := 13, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 388 56 25 34 77 141 269), lower := (rows 7 98 388 56 25 34 64 128 256), losses := [] }

theorem u3478 : Upper (D 5) (R 5) [6,96,384,48,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3478
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3479 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 98 388 56 25 36 75 139 267), lower := (rows 7 98 388 56 25 36 64 128 256), losses := [] }

theorem u3479 : Upper (D 5) (R 5) [6,96,384,48,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3479
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u3479
end Delivery.IrregularNine14.P05
