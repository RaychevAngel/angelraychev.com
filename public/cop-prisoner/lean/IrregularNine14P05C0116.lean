import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0057
import IrregularNine14P05C0058

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6960 : Route 9 := (fun mask => (mask,id))

def c6960 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6960 : Upper (D 5) (R 5) [6,96,384,33,12] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,12] 13 (by decide) (choices 1) [1,2,8,16] r6960 c6960
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3469
  · exact u3470
  · exact u3471
  · exact u3472

def b6961 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 98 388 44 19 57 89 153 281), lower := (rows 7 98 388 44 19 32 64 128 256), losses := [] }

theorem u6961 : Upper (D 5) (R 5) [6,96,384,36,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6961
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6962 : Route 9 := (fun mask => (mask,id))

def c6962 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6962 : Upper (D 5) (R 5) [6,96,384,36,9] 13 := by
  apply FastRouting.sound _ _ [6,96,384,36,9] 13 (by decide) (choices 1) [1,2,8,16] r6962 c6962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3473
  · exact u3474
  · exact u3475
  · exact u3476

def b6963 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 389, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 98 388 44 26 57 89 153 281), lower := (rows 7 98 388 44 26 32 64 128 256), losses := [] }

theorem u6963 : Upper (D 5) (R 5) [6,96,384,36,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6963
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6964 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 16, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 98 388 56 19 45 77 141 269), lower := (rows 7 98 388 56 19 32 64 128 256), losses := [] }

theorem u6964 : Upper (D 5) (R 5) [6,96,384,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6964
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6965 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 16, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 98 388 56 21 43 75 139 267), lower := (rows 7 98 388 56 21 32 64 128 256), losses := [] }

theorem u6965 : Upper (D 5) (R 5) [6,96,384,48,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6965
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6966 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 16, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 98 388 56 22 41 73 137 265), lower := (rows 7 98 388 56 22 32 64 128 256), losses := [] }

theorem u6966 : Upper (D 5) (R 5) [6,96,384,48,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6966
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6967 : Route 9 := (fun mask => (mask,id))

def c6967 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6967 : Upper (D 5) (R 5) [6,96,384,48,9] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,9] 13 (by decide) (choices 1) [1,2,4,8] r6967 c6967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3477
  · exact u3478
  · exact u3479
  · exact u3480

def b6968 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 24, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 98 388 56 26 45 77 141 269), lower := (rows 7 98 388 56 26 32 64 128 256), losses := [] }

theorem u6968 : Upper (D 5) (R 5) [6,96,384,48,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6968
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6969 : Route 9 := (fun mask => (mask,id))

def c6969 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6969 : Upper (D 5) (R 5) [6,96,384,48,12] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,12] 13 (by decide) (choices 1) [1,2,8] r6969 c6969
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3481
  · exact u3482
  · exact u3483

def b6970 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 44 73 22 428 460 396 396), lower := (rows 19 35 44 73 22 32 64 128 256), losses := [] }

theorem u6970 : Upper (D 5) (R 5) [18,33,40,65,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6970
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6971 : PairBound 9 := { available := 388, camps := [{ cop := 2, region := 19, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 44 73 26 420 452 388 388), lower := (rows 19 35 44 73 26 32 64 128 256), losses := [] }

theorem u6971 : Upper (D 5) (R 5) [18,33,40,65,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6971
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6972 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 35 44 73 28 422 454 390 390), lower := (rows 19 35 44 73 28 32 64 128 256), losses := [] }

theorem u6972 : Upper (D 5) (R 5) [18,33,40,65,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6972
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6973 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 73 146 300 332 396 268), lower := (rows 19 35 44 73 146 32 64 128 256), losses := [] }

theorem u6973 : Upper (D 5) (R 5) [18,33,40,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6973
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6974 : Route 9 := (fun mask => (mask,id))

def c6974 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6974 : Upper (D 5) (R 5) [18,33,40,65,132] 13 := by
  apply FastRouting.sound _ _ [18,33,40,65,132] 13 (by decide) (choices 1) [2,4,8,256] r6974 c6974
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3484
  · exact u3485
  · exact u3486
  · exact u3487

def r6975 : Route 9 := (fun mask => (mask,id))

def c6975 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6975 : Upper (D 5) (R 5) [18,33,40,65,136] 13 := by
  apply FastRouting.sound _ _ [18,33,40,65,136] 13 (by decide) (choices 1) [2,4,256] r6975 c6975
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3488
  · exact u3489
  · exact u3490

def r6976 : Route 9 := (fun mask => (mask,id))

def c6976 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6976 : Upper (D 5) (R 5) [18,33,40,65,384] 13 := by
  apply FastRouting.sound _ _ [18,33,40,65,384] 13 (by decide) (choices 1) [2,4,8] r6976 c6976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3491
  · exact u3492
  · exact u3493

def b6977 : PairBound 9 := { available := 396, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 44 74 21 428 460 396 396), lower := (rows 19 35 44 74 21 32 64 128 256), losses := [] }

theorem u6977 : Upper (D 5) (R 5) [18,33,40,66,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6977
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6978 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 17, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 35 44 74 25 420 452 388 388), lower := (rows 19 35 44 74 25 32 64 128 256), losses := [] }

theorem u6978 : Upper (D 5) (R 5) [18,33,40,66,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6978
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6979 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 35 44 74 28 421 453 389 389), lower := (rows 19 35 44 74 28 32 64 128 256), losses := [] }

theorem u6979 : Upper (D 5) (R 5) [18,33,40,66,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6979
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6980 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 364, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 44 74 145 300 332 396 268), lower := (rows 19 35 44 74 145 32 64 128 256), losses := [] }

theorem u6980 : Upper (D 5) (R 5) [18,33,40,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6980
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6981 : Route 9 := (fun mask => (mask,id))

def c6981 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6981 : Upper (D 5) (R 5) [18,33,40,66,132] 13 := by
  apply FastRouting.sound _ _ [18,33,40,66,132] 13 (by decide) (choices 1) [1,4,8,256] r6981 c6981
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3494
  · exact u3495
  · exact u3496
  · exact u3497

def r6982 : Route 9 := (fun mask => (mask,id))

def c6982 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6982 : Upper (D 5) (R 5) [18,33,40,66,136] 13 := by
  apply FastRouting.sound _ _ [18,33,40,66,136] 13 (by decide) (choices 1) [1,4,256] r6982 c6982
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3498
  · exact u3499
  · exact u3500

def r6983 : Route 9 := (fun mask => (mask,id))

def c6983 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6983 : Upper (D 5) (R 5) [18,33,40,66,384] 13 := by
  apply FastRouting.sound _ _ [18,33,40,66,384] 13 (by decide) (choices 1) [1,4,8] r6983 c6983
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3501
  · exact u3502
  · exact u3503

def b6984 : PairBound 9 := { available := 396, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 76 19 428 460 396 396), lower := (rows 19 35 44 76 19 32 64 128 256), losses := [] }

theorem u6984 : Upper (D 5) (R 5) [18,33,40,68,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6984
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6985 : PairBound 9 := { available := 394, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 44 76 21 426 458 394 394), lower := (rows 19 35 44 76 21 32 64 128 256), losses := [] }

theorem u6985 : Upper (D 5) (R 5) [18,33,40,68,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6985
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6986 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 44 76 22 425 457 393 393), lower := (rows 19 35 44 76 22 32 64 128 256), losses := [] }

theorem u6986 : Upper (D 5) (R 5) [18,33,40,68,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6986
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6987 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 19, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 44 76 25 422 454 390 390), lower := (rows 19 35 44 76 25 32 64 128 256), losses := [] }

theorem u6987 : Upper (D 5) (R 5) [18,33,40,68,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6987
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6988 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 19, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 44 76 26 421 453 389 389), lower := (rows 19 35 44 76 26 32 64 128 256), losses := [] }

theorem u6988 : Upper (D 5) (R 5) [18,33,40,68,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6988
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6989 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 419, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 76 28 419 451 387 387), lower := (rows 19 35 44 76 28 32 64 128 256), losses := [] }

theorem u6989 : Upper (D 5) (R 5) [18,33,40,68,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6989
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6990 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 364, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 44 76 145 302 334 398 270), lower := (rows 19 35 44 76 145 32 64 128 256), losses := [] }

theorem u6990 : Upper (D 5) (R 5) [18,33,40,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6990
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6991 : PairBound 9 := { available := 269, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 76 146 301 333 397 269), lower := (rows 19 35 44 76 146 32 64 128 256), losses := [] }

theorem u6991 : Upper (D 5) (R 5) [18,33,40,68,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6991
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r6992 : Route 9 := (fun mask => (mask,id))

def c6992 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6992 : Upper (D 5) (R 5) [18,33,40,68,132] 13 := by
  apply FastRouting.sound _ _ [18,33,40,68,132] 13 (by decide) (choices 1) [1,2,8,256] r6992 c6992
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3504
  · exact u3505
  · exact u3506
  · exact u3507

def r6993 : Route 9 := (fun mask => (mask,id))

def c6993 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6993 : Upper (D 5) (R 5) [18,33,40,68,136] 13 := by
  apply FastRouting.sound _ _ [18,33,40,68,136] 13 (by decide) (choices 1) [1,2,4,256] r6993 c6993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3508
  · exact u3509
  · exact u3510
  · exact u3511

def r6994 : Route 9 := (fun mask => (mask,id))

def c6994 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6994 : Upper (D 5) (R 5) [18,33,40,68,384] 13 := by
  apply FastRouting.sound _ _ [18,33,40,68,384] 13 (by decide) (choices 1) [1,2,4,8] r6994 c6994
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3512
  · exact u3513
  · exact u3514
  · exact u3515

def b6995 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 17, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 200 19 300 332 396 268), lower := (rows 19 35 44 200 19 32 64 128 256), losses := [] }

theorem u6995 : Upper (D 5) (R 5) [18,33,40,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6995
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6996 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 44 200 21 302 334 398 270), lower := (rows 19 35 44 200 21 32 64 128 256), losses := [] }

theorem u6996 : Upper (D 5) (R 5) [18,33,40,192,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6996
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6997 : PairBound 9 := { available := 269, camps := [{ cop := 2, region := 19, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 19 35 44 200 22 301 333 397 269), lower := (rows 19 35 44 200 22 32 64 128 256), losses := [] }

theorem u6997 : Upper (D 5) (R 5) [18,33,40,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6997
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6998 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 19, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 44 200 25 294 326 390 262), lower := (rows 19 35 44 200 25 32 64 128 256), losses := [] }

theorem u6998 : Upper (D 5) (R 5) [18,33,40,192,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6998
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b6999 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 19, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 19 35 44 200 26 293 325 389 261), lower := (rows 19 35 44 200 26 32 64 128 256), losses := [] }

theorem u6999 : Upper (D 5) (R 5) [18,33,40,192,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b6999
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7000 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 35 44 200 28 295 327 391 263), lower := (rows 19 35 44 200 28 32 64 128 256), losses := [] }

theorem u7000 : Upper (D 5) (R 5) [18,33,40,192,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7000
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7001 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 236, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 19 35 44 200 273 46 78 142 270), lower := (rows 19 35 44 200 273 32 64 128 256), losses := [] }

theorem u7001 : Upper (D 5) (R 5) [18,33,40,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7001
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7002 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 44 200 274 45 77 141 269), lower := (rows 19 35 44 200 274 32 64 128 256), losses := [] }

theorem u7002 : Upper (D 5) (R 5) [18,33,40,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7002
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7003 : Route 9 := (fun mask => (mask,id))

def c7003 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7003 : Upper (D 5) (R 5) [18,33,40,192,260] 13 := by
  apply FastRouting.sound _ _ [18,33,40,192,260] 13 (by decide) (choices 1) [1,2,4,8] r7003 c7003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3516
  · exact u3517
  · exact u3518
  · exact u3519

def r7004 : Route 9 := (fun mask => (mask,id))

def c7004 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7004 : Upper (D 5) (R 5) [18,33,40,192,264] 13 := by
  apply FastRouting.sound _ _ [18,33,40,192,264] 13 (by decide) (choices 1) [1,2,4] r7004 c7004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3520
  · exact u3521
  · exact u3522

def b7005 : PairBound 9 := { available := 300, camps := [], pairs := [(3,0),(4,0)], upper := (rows 19 35 69 138 28 300 364 428 300), lower := (rows 19 35 69 138 28 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 20 52 84 148 276), good := (rows 506 42 508 138 508 32 64 128 256) }] }

theorem u7005 : Upper (D 5) (R 5) [18,33,65,130,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7005
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7006 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 138 52 300 332 396 268), lower := (rows 19 35 69 138 52 32 64 128 256), losses := [] }

theorem u7006 : Upper (D 5) (R 5) [18,33,65,130,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7006
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7007 : PairBound 9 := { available := 268, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 138 56 300 332 396 268), lower := (rows 19 35 69 138 56 32 64 128 256), losses := [] }

theorem u7007 : Upper (D 5) (R 5) [18,33,65,130,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7007
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7008 : Route 9 := (fun mask => (mask,id))

def c7008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7008 : Upper (D 5) (R 5) [18,33,65,130,260] 13 := by
  apply FastRouting.sound _ _ [18,33,65,130,260] 13 (by decide) (choices 1) [4,8] r7008 c7008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3523
  · exact u3524

def r7009 : Route 9 := (fun mask => (mask,id))

def c7009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7009 : Upper (D 5) (R 5) [18,33,65,130,264] 13 := by
  apply FastRouting.sound _ _ [18,33,65,130,264] 13 (by decide) (choices 1) [4,8] r7009 c7009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3525
  · exact u3526

def b7010 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 138 304 44 76 140 268), lower := (rows 19 35 69 138 304 32 64 128 256), losses := [] }

theorem u7010 : Upper (D 5) (R 5) [18,33,65,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7010
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7011 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 140 22 296 360 424 296), lower := (rows 19 35 69 140 22 32 64 128 256), losses := [] }

theorem u7011 : Upper (D 5) (R 5) [18,33,65,132,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7011
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7012 : PairBound 9 := { available := 300, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 140 26 300 364 428 300), lower := (rows 19 35 69 140 26 32 64 128 256), losses := [] }

theorem u7012 : Upper (D 5) (R 5) [18,33,65,132,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7012
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7013 : PairBound 9 := { available := 298, camps := [{ cop := 3, region := 16, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 35 69 140 28 298 362 426 298), lower := (rows 19 35 69 140 28 32 64 128 256), losses := [] }

theorem u7013 : Upper (D 5) (R 5) [18,33,65,132,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7013
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7014 : PairBound 9 := { available := 268, camps := [{ cop := 5, region := 19, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 140 50 300 332 396 268), lower := (rows 19 35 69 140 50 32 64 128 256), losses := [] }

theorem u7014 : Upper (D 5) (R 5) [18,33,65,132,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7014
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7015 : PairBound 9 := { available := 266, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 140 52 298 330 394 266), lower := (rows 19 35 69 140 52 32 64 128 256), losses := [] }

theorem u7015 : Upper (D 5) (R 5) [18,33,65,132,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7015
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7016 : PairBound 9 := { available := 270, camps := [{ cop := 4, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 140 56 302 334 398 270), lower := (rows 19 35 69 140 56 32 64 128 256), losses := [] }

theorem u7016 : Upper (D 5) (R 5) [18,33,65,132,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7016
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b7017 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 1, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 19 35 69 140 274 44 108 172 300), lower := (rows 19 35 69 140 274 32 64 128 256), losses := [] }

theorem u7017 : Upper (D 5) (R 5) [18,33,65,132,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b7017
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r7018 : Route 9 := (fun mask => (mask,id))

def c7018 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7018 : Upper (D 5) (R 5) [18,33,65,132,260] 13 := by
  apply FastRouting.sound _ _ [18,33,65,132,260] 13 (by decide) (choices 1) [2,8] r7018 c7018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3527
  · exact u3528

def r7019 : Route 9 := (fun mask => (mask,id))

def c7019 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7019 : Upper (D 5) (R 5) [18,33,65,132,264] 13 := by
  apply FastRouting.sound _ _ [18,33,65,132,264] 13 (by decide) (choices 1) [2,4,8] r7019 c7019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3529
  · exact u3530
  · exact u3531

#print axioms u7019
end Delivery.IrregularNine14.P05
