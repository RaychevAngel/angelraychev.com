import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0017

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3480 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 56, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 98 388 56 25 40 71 135 263), lower := (rows 7 98 388 56 25 40 64 128 256), losses := [] }

theorem u3480 : Upper (D 5) (R 5) [6,96,384,48,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3480
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3481 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 98 388 56 28 33 75 139 267), lower := (rows 7 98 388 56 28 33 64 128 256), losses := [] }

theorem u3481 : Upper (D 5) (R 5) [6,96,384,48,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3481
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3482 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 98 388 56 28 34 73 137 265), lower := (rows 7 98 388 56 28 34 64 128 256), losses := [] }

theorem u3482 : Upper (D 5) (R 5) [6,96,384,48,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3482
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3483 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 389, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 98 388 56 28 40 67 131 259), lower := (rows 7 98 388 56 28 40 64 128 256), losses := [] }

theorem u3483 : Upper (D 5) (R 5) [6,96,384,48,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3483
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3484 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 73 148 34 332 396 268), lower := (rows 19 35 44 73 148 34 64 128 256), losses := [] }

theorem u3484 : Upper (D 5) (R 5) [18,33,40,65,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3484
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3485 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 328, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 19 35 44 73 148 36 330 394 266), lower := (rows 19 35 44 73 148 36 64 128 256), losses := [] }

theorem u3485 : Upper (D 5) (R 5) [18,33,40,65,132,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3485
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3486 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 403, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 44 73 148 40 326 390 262), lower := (rows 19 35 44 73 148 40 64 128 256), losses := [] }

theorem u3486 : Upper (D 5) (R 5) [18,33,40,65,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3486
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3487 : Route 9 := (fun mask => (mask,id))

def c3487 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3487 : Upper (D 5) (R 5) [18,33,40,65,132,256] 13 := by
  apply FastRouting.sound _ _ [18,33,40,65,132,256] 13 (by decide) (choices 1) [2,4,8] r3487 c3487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1038
  · exact u1039
  · exact u1040

def b3488 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 73 152 34 324 388 260), lower := (rows 19 35 44 73 152 34 64 128 256), losses := [] }

theorem u3488 : Upper (D 5) (R 5) [18,33,40,65,136,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3488
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3489 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 35 44 73 152 36 326 390 262), lower := (rows 19 35 44 73 152 36 64 128 256), losses := [] }

theorem u3489 : Upper (D 5) (R 5) [18,33,40,65,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3489
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3490 : PairBound 9 := { available := 6, camps := [], pairs := [(2,0)], upper := (rows 19 35 44 73 152 288 70 134 262), lower := (rows 19 35 44 73 152 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 28 8 24 299 65 129 257), good := (rows 502 482 60 508 188 288 64 128 288) }] }

theorem u3490 : Upper (D 5) (R 5) [18,33,40,65,136,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3490
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3491 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 73 400 34 76 140 268), lower := (rows 19 35 44 73 400 34 64 128 256), losses := [] }

theorem u3491 : Upper (D 5) (R 5) [18,33,40,65,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3491
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3492 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 35 44 73 400 36 78 142 270), lower := (rows 19 35 44 73 400 36 64 128 256), losses := [] }

theorem u3492 : Upper (D 5) (R 5) [18,33,40,65,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3492
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3493 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 403, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 44 73 400 40 70 134 262), lower := (rows 19 35 44 73 400 40 64 128 256), losses := [] }

theorem u3493 : Upper (D 5) (R 5) [18,33,40,65,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3493
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3494 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 74 148 33 332 396 268), lower := (rows 19 35 44 74 148 33 64 128 256), losses := [] }

theorem u3494 : Upper (D 5) (R 5) [18,33,40,66,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3494
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3495 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 328, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 19 35 44 74 148 36 329 393 265), lower := (rows 19 35 44 74 148 36 64 128 256), losses := [] }

theorem u3495 : Upper (D 5) (R 5) [18,33,40,66,132,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3495
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3496 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 403, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 44 74 148 40 325 389 261), lower := (rows 19 35 44 74 148 40 64 128 256), losses := [] }

theorem u3496 : Upper (D 5) (R 5) [18,33,40,66,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3496
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3497 : Route 9 := (fun mask => (mask,id))

def c3497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3497 : Upper (D 5) (R 5) [18,33,40,66,132,256] 13 := by
  apply FastRouting.sound _ _ [18,33,40,66,132,256] 13 (by decide) (choices 1) [1,4,8] r3497 c3497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1041
  · exact u1042
  · exact u1043

def b3498 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 74 152 33 324 388 260), lower := (rows 19 35 44 74 152 33 64 128 256), losses := [] }

theorem u3498 : Upper (D 5) (R 5) [18,33,40,66,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3498
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3499 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 35 44 74 152 36 325 389 261), lower := (rows 19 35 44 74 152 36 64 128 256), losses := [] }

theorem u3499 : Upper (D 5) (R 5) [18,33,40,66,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3499
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3500 : Route 9 := (fun mask => (mask,id))

def c3500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3500 : Upper (D 5) (R 5) [18,33,40,66,136,256] 13 := by
  apply FastRouting.sound _ _ [18,33,40,66,136,256] 13 (by decide) (choices 1) [1,4] r3500 c3500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1044
  · exact u1045

def b3501 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 74 400 33 76 140 268), lower := (rows 19 35 44 74 400 33 64 128 256), losses := [] }

theorem u3501 : Upper (D 5) (R 5) [18,33,40,66,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3501
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3502 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 35 44 74 400 36 77 141 269), lower := (rows 19 35 44 74 400 36 64 128 256), losses := [] }

theorem u3502 : Upper (D 5) (R 5) [18,33,40,66,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3502
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3503 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 403, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 44 74 400 40 69 133 261), lower := (rows 19 35 44 74 400 40 64 128 256), losses := [] }

theorem u3503 : Upper (D 5) (R 5) [18,33,40,66,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3503
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3504 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 76 148 33 330 394 266), lower := (rows 19 35 44 76 148 33 64 128 256), losses := [] }

theorem u3504 : Upper (D 5) (R 5) [18,33,40,68,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3504
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3505 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 76 148 34 329 393 265), lower := (rows 19 35 44 76 148 34 64 128 256), losses := [] }

theorem u3505 : Upper (D 5) (R 5) [18,33,40,68,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3505
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3506 : PairBound 9 := { available := 259, camps := [{ cop := 6, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 35 44 76 148 40 323 387 259), lower := (rows 19 35 44 76 148 40 64 128 256), losses := [] }

theorem u3506 : Upper (D 5) (R 5) [18,33,40,68,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3506
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3507 : Route 9 := (fun mask => (mask,id))

def c3507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3507 : Upper (D 5) (R 5) [18,33,40,68,132,256] 13 := by
  apply FastRouting.sound _ _ [18,33,40,68,132,256] 13 (by decide) (choices 1) [1,2,8] r3507 c3507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1046
  · exact u1047
  · exact u1048

def b3508 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 76 152 33 326 390 262), lower := (rows 19 35 44 76 152 33 64 128 256), losses := [] }

theorem u3508 : Upper (D 5) (R 5) [18,33,40,68,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3508
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3509 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 76 152 34 325 389 261), lower := (rows 19 35 44 76 152 34 64 128 256), losses := [] }

theorem u3509 : Upper (D 5) (R 5) [18,33,40,68,136,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3509
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3510 : PairBound 9 := { available := 259, camps := [{ cop := 6, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 35 44 76 152 36 323 387 259), lower := (rows 19 35 44 76 152 36 64 128 256), losses := [] }

theorem u3510 : Upper (D 5) (R 5) [18,33,40,68,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3510
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3511 : Route 9 := (fun mask => (mask,id))

def c3511 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3511 : Upper (D 5) (R 5) [18,33,40,68,136,256] 13 := by
  apply FastRouting.sound _ _ [18,33,40,68,136,256] 13 (by decide) (choices 1) [1,2,4] r3511 c3511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1049
  · exact u1050
  · exact u1051

def b3512 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 76 400 33 78 142 270), lower := (rows 19 35 44 76 400 33 64 128 256), losses := [] }

theorem u3512 : Upper (D 5) (R 5) [18,33,40,68,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3512
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3513 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 76 400 34 77 141 269), lower := (rows 19 35 44 76 400 34 64 128 256), losses := [] }

theorem u3513 : Upper (D 5) (R 5) [18,33,40,68,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3513
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3514 : PairBound 9 := { available := 11, camps := [{ cop := 6, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 35 44 76 400 36 75 139 267), lower := (rows 19 35 44 76 400 36 64 128 256), losses := [] }

theorem u3514 : Upper (D 5) (R 5) [18,33,40,68,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3514
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3515 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 35 44 76 400 40 71 135 263), lower := (rows 19 35 44 76 400 40 64 128 256), losses := [] }

theorem u3515 : Upper (D 5) (R 5) [18,33,40,68,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3515
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3516 : PairBound 9 := { available := 14, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 200 276 33 78 142 270), lower := (rows 19 35 44 200 276 33 64 128 256), losses := [] }

theorem u3516 : Upper (D 5) (R 5) [18,33,40,192,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3516
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3517 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 200 276 34 77 141 269), lower := (rows 19 35 44 200 276 34 64 128 256), losses := [] }

theorem u3517 : Upper (D 5) (R 5) [18,33,40,192,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3517
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3518 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 200, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 19 35 44 200 276 36 75 139 267), lower := (rows 19 35 44 200 276 36 64 128 256), losses := [] }

theorem u3518 : Upper (D 5) (R 5) [18,33,40,192,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3518
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3519 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 275, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 44 200 276 40 71 135 263), lower := (rows 19 35 44 200 276 40 64 128 256), losses := [] }

theorem u3519 : Upper (D 5) (R 5) [18,33,40,192,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3519
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3520 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 200 280 33 70 134 262), lower := (rows 19 35 44 200 280 33 64 128 256), losses := [] }

theorem u3520 : Upper (D 5) (R 5) [18,33,40,192,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3520
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3521 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 200 280 34 69 133 261), lower := (rows 19 35 44 200 280 34 64 128 256), losses := [] }

theorem u3521 : Upper (D 5) (R 5) [18,33,40,192,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3521
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3522 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 35 44 200 280 36 71 135 263), lower := (rows 19 35 44 200 280 36 64 128 256), losses := [] }

theorem u3522 : Upper (D 5) (R 5) [18,33,40,192,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3522
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3523 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 136, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 35 69 138 276 36 104 168 296), lower := (rows 19 35 69 138 276 36 64 128 256), losses := [] }

theorem u3523 : Upper (D 5) (R 5) [18,33,65,130,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3523
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3524 : Route 9 := (fun mask => (mask,id))

def c3524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3524 : Upper (D 5) (R 5) [18,33,65,130,260,8] 13 := by
  apply FastRouting.sound _ _ [18,33,65,130,260,8] 13 (by decide) (choices 1) [4,8,32] r3524 c3524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1052
  · exact u1053
  · exact u1054

def r3525 : Route 9 := (fun mask => (mask,id))

def c3525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3525 : Upper (D 5) (R 5) [18,33,65,130,264,4] 13 := by
  apply FastRouting.sound _ _ [18,33,65,130,264,4] 13 (by decide) (choices 1) [4,8,32] r3525 c3525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1055
  · exact u1056
  · exact u1057

def b3526 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 35, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 69 138 280 40 100 164 292), lower := (rows 19 35 69 138 280 40 64 128 256), losses := [] }

theorem u3526 : Upper (D 5) (R 5) [18,33,65,130,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3526
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3527 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 140 276 34 104 168 296), lower := (rows 19 35 69 140 276 34 64 128 256), losses := [] }

theorem u3527 : Upper (D 5) (R 5) [18,33,65,132,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3527
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3528 : Route 9 := (fun mask => (mask,id))

def c3528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3528 : Upper (D 5) (R 5) [18,33,65,132,260,8] 13 := by
  apply FastRouting.sound _ _ [18,33,65,132,260,8] 13 (by decide) (choices 1) [2,8,32] r3528 c3528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1058
  · exact u1059
  · exact u1060

def b3529 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 140 280 34 108 172 300), lower := (rows 19 35 69 140 280 34 64 128 256), losses := [] }

theorem u3529 : Upper (D 5) (R 5) [18,33,65,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3529
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3530 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 34, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 69 140 280 36 106 170 298), lower := (rows 19 35 69 140 280 36 64 128 256), losses := [{ target := 3, region := (rows 17 22 4 0 16 44 64 128 256), good := (rows 19 35 103 166 307 38 64 128 256) }] }

theorem u3530 : Upper (D 5) (R 5) [18,33,65,132,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3530
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3531 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 35, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 69 140 280 40 102 166 294), lower := (rows 19 35 69 140 280 40 64 128 256), losses := [] }

theorem u3531 : Upper (D 5) (R 5) [18,33,65,132,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3531
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3532 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 168 28 34 332 396 268), lower := (rows 19 35 69 168 28 34 64 128 256), losses := [] }

theorem u3532 : Upper (D 5) (R 5) [18,33,65,160,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3532
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3533 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 392, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 35 69 168 28 36 330 394 266), lower := (rows 19 35 69 168 28 36 64 128 256), losses := [] }

theorem u3533 : Upper (D 5) (R 5) [18,33,65,160,12,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3533
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3534 : PairBound 9 := { available := 262, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 35 69 168 28 40 326 390 262), lower := (rows 19 35 69 168 28 40 64 128 256), losses := [] }

theorem u3534 : Upper (D 5) (R 5) [18,33,65,160,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3534
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3535 : Route 9 := (fun mask => (mask,id))

def c3535 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3535 : Upper (D 5) (R 5) [18,33,65,160,12,256] 13 := by
  apply FastRouting.sound _ _ [18,33,65,160,12,256] 13 (by decide) (choices 1) [2,4,8] r3535 c3535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1061
  · exact u1062
  · exact u1063

def b3536 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 168 276 34 76 140 268), lower := (rows 19 35 69 168 276 34 64 128 256), losses := [] }

theorem u3536 : Upper (D 5) (R 5) [18,33,65,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3536
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3537 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 136, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 35 69 168 276 36 74 138 266), lower := (rows 19 35 69 168 276 36 64 128 256), losses := [] }

theorem u3537 : Upper (D 5) (R 5) [18,33,65,160,260,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3537
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3538 : PairBound 9 := { available := 14, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 35 69 168 276 40 78 142 270), lower := (rows 19 35 69 168 276 40 64 128 256), losses := [] }

theorem u3538 : Upper (D 5) (R 5) [18,33,65,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3538
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3539 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 35, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 168 280 34 76 140 268), lower := (rows 19 35 69 168 280 34 64 128 256), losses := [] }

theorem u3539 : Upper (D 5) (R 5) [18,33,65,160,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3539
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u3539
end Delivery.IrregularNine14.P05
