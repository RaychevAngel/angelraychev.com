import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0032
import IrregularNine14P01C0033

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m5520_2 : Upper (D 1) (R 1) [304,68,136,3,64,2] 13 :=
  permutation_upper _ _ _ [304,68,136,3,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1962

theorem m5520_16 : Upper (D 1) (R 1) [304,68,136,3,64,16] 13 :=
  permutation_upper _ _ _ [304,68,136,3,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1964

def r5520 : Route 9 := (fun mask => (mask,id))

def c5520 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5520 : Upper (D 1) (R 1) [304,68,136,3,64] 13 := by
  apply FastRouting.sound _ _ [304,68,136,3,64] 13 (by decide) (choices 1) [2,16,128] r5520 c5520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5520_2
  · exact m5520_16
  · exact u1966

theorem m5521_2 : Upper (D 1) (R 1) [304,68,136,3,128,2] 13 :=
  permutation_upper _ _ _ [304,68,136,3,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1963

theorem m5521_16 : Upper (D 1) (R 1) [304,68,136,3,128,16] 13 :=
  permutation_upper _ _ _ [304,68,136,3,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1965

theorem m5521_64 : Upper (D 1) (R 1) [304,68,136,3,128,64] 13 :=
  permutation_upper _ _ _ [304,68,136,3,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1966

def r5521 : Route 9 := (fun mask => (mask,id))

def c5521 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5521 : Upper (D 1) (R 1) [304,68,136,3,128] 13 := by
  apply FastRouting.sound _ _ [304,68,136,3,128] 13 (by decide) (choices 1) [2,16,64] r5521 c5521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5521_2
  · exact m5521_16
  · exact m5521_64

def b5522 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 70 140 26 17 226 226 226 482), lower := (rows 305 70 140 26 17 32 64 128 256), losses := [] }

theorem u5522 : Upper (D 1) (R 1) [304,68,136,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5522
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5523 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 70 140 26 18 225 225 225 481), lower := (rows 305 70 140 26 18 32 64 128 256), losses := [] }

theorem u5523 : Upper (D 1) (R 1) [304,68,136,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5523
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5524 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 140 26 48 227 195 195 451), lower := (rows 305 70 140 26 48 32 64 128 256), losses := [] }

theorem u5524 : Upper (D 1) (R 1) [304,68,136,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5524
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5525 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 305 70 140 26 80 163 227 163 419), lower := (rows 305 70 140 26 80 32 64 128 256), losses := [] }

theorem u5525 : Upper (D 1) (R 1) [304,68,136,18,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5525
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5526 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 140 26 144 99 99 227 355), lower := (rows 305 70 140 26 144 32 64 128 256), losses := [] }

theorem u5526 : Upper (D 1) (R 1) [304,68,136,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5526
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5527 : Route 9 := (fun mask => (mask,id))

def c5527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5527 : Upper (D 1) (R 1) [304,68,144,3,2] 13 := by
  apply FastRouting.sound _ _ [304,68,144,3,2] 13 (by decide) (choices 1) [8,64,128] r5527 c5527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1967
  · exact u1968
  · exact u1969

def b5528 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 70 148 11 24 226 226 226 482), lower := (rows 305 70 148 11 24 32 64 128 256), losses := [] }

theorem u5528 : Upper (D 1) (R 1) [304,68,144,3,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5528
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5529 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 148 11 48 234 202 202 458), lower := (rows 305 70 148 11 48 32 64 128 256), losses := [] }

theorem u5529 : Upper (D 1) (R 1) [304,68,144,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5529
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5530 : Route 9 := (fun mask => (mask,id))

def c5530 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5530 : Upper (D 1) (R 1) [304,68,144,3,64] 13 := by
  apply FastRouting.sound _ _ [304,68,144,3,64] 13 (by decide) (choices 1) [2,8,128] r5530 c5530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1970
  · exact u1971
  · exact u1972

def b5531 : PairBound 9 := { available := 106, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 148 11 144 106 106 234 362), lower := (rows 305 70 148 11 144 32 64 128 256), losses := [] }

theorem u5531 : Upper (D 1) (R 1) [304,68,144,3,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5531
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5532 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 305 70 148 42 17 234 202 202 458), lower := (rows 305 70 148 42 17 32 64 128 256), losses := [] }

theorem u5532 : Upper (D 1) (R 1) [304,68,144,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5532
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5533 : Route 9 := (fun mask => (mask,id))

def c5533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5533 : Upper (D 1) (R 1) [304,68,144,34,2] 13 := by
  apply FastRouting.sound _ _ [304,68,144,34,2] 13 (by decide) (choices 1) [1,8,64,128] r5533 c5533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1973
  · exact u1974
  · exact u1975
  · exact u1976

def b5534 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 305 70 148 42 24 227 195 195 451), lower := (rows 305 70 148 42 24 32 64 128 256), losses := [] }

theorem u5534 : Upper (D 1) (R 1) [304,68,144,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5534
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5535 : Route 9 := (fun mask => (mask,id))

def c5535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5535 : Upper (D 1) (R 1) [304,68,144,34,64] 13 := by
  apply FastRouting.sound _ _ [304,68,144,34,64] 13 (by decide) (choices 1) [1,2,8,128] r5535 c5535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1977
  · exact u1978
  · exact u1979
  · exact u1980

def b5536 : PairBound 9 := { available := 75, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 148 42 144 107 75 203 331), lower := (rows 305 70 148 42 144 32 64 128 256), losses := [] }

theorem u5536 : Upper (D 1) (R 1) [304,68,144,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5536
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5537 : Route 9 := (fun mask => (mask,id))

def c5537 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5537 : Upper (D 1) (R 1) [304,68,144,65,2] 13 := by
  apply FastRouting.sound _ _ [304,68,144,65,2] 13 (by decide) (choices 1) [2,8,128] r5537 c5537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1981
  · exact u1982
  · exact u1983

def b5538 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 70 148 73 24 162 226 162 418), lower := (rows 305 70 148 73 24 32 64 128 256), losses := [] }

theorem u5538 : Upper (D 1) (R 1) [304,68,144,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5538
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5539 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 148 73 48 170 202 138 394), lower := (rows 305 70 148 73 48 32 64 128 256), losses := [] }

theorem u5539 : Upper (D 1) (R 1) [304,68,144,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5539
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5540 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 148 73 144 42 106 170 298), lower := (rows 305 70 148 73 144 32 64 128 256), losses := [] }

theorem u5540 : Upper (D 1) (R 1) [304,68,144,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5540
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5541 : PairBound 9 := { available := 138, camps := [], pairs := [], upper := (rows 305 70 148 104 17 170 202 138 394), lower := (rows 305 70 148 104 17 32 64 128 256), losses := [] }

theorem u5541 : Upper (D 1) (R 1) [304,68,144,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5541
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5542 : Route 9 := (fun mask => (mask,id))

def c5542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5542 : Upper (D 1) (R 1) [304,68,144,96,2] 13 := by
  apply FastRouting.sound _ _ [304,68,144,96,2] 13 (by decide) (choices 1) [1,2,8,128] r5542 c5542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1984
  · exact u1985
  · exact u1986
  · exact u1987

def b5543 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 70 148 104 24 163 195 131 387), lower := (rows 305 70 148 104 24 32 64 128 256), losses := [] }

theorem u5543 : Upper (D 1) (R 1) [304,68,144,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5543
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5544 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 148 104 144 43 75 139 267), lower := (rows 305 70 148 104 144 32 64 128 256), losses := [] }

theorem u5544 : Upper (D 1) (R 1) [304,68,144,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5544
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5545 : Route 9 := (fun mask => (mask,id))

def c5545 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5545 : Upper (D 1) (R 1) [304,68,144,129,2] 13 := by
  apply FastRouting.sound _ _ [304,68,144,129,2] 13 (by decide) (choices 1) [2,8,64] r5545 c5545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1988
  · exact u1989
  · exact u1990

def b5546 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 305 70 148 137 24 98 98 226 354), lower := (rows 305 70 148 137 24 32 64 128 256), losses := [] }

theorem u5546 : Upper (D 1) (R 1) [304,68,144,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5546
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5547 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 148 137 48 106 74 202 330), lower := (rows 305 70 148 137 48 32 64 128 256), losses := [] }

theorem u5547 : Upper (D 1) (R 1) [304,68,144,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5547
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5548 : Route 9 := (fun mask => (mask,id))

def c5548 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5548 : Upper (D 1) (R 1) [304,68,144,129,64] 13 := by
  apply FastRouting.sound _ _ [304,68,144,129,64] 13 (by decide) (choices 1) [2,8] r5548 c5548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1991
  · exact u1992

def b5549 : PairBound 9 := { available := 74, camps := [], pairs := [], upper := (rows 305 70 148 168 17 106 74 202 330), lower := (rows 305 70 148 168 17 32 64 128 256), losses := [] }

theorem u5549 : Upper (D 1) (R 1) [304,68,144,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5549
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5550 : Route 9 := (fun mask => (mask,id))

def c5550 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5550 : Upper (D 1) (R 1) [304,68,144,160,2] 13 := by
  apply FastRouting.sound _ _ [304,68,144,160,2] 13 (by decide) (choices 1) [1,2,8,64] r5550 c5550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1993
  · exact u1994
  · exact u1995
  · exact u1996

def b5551 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 305 70 148 168 24 99 67 195 323), lower := (rows 305 70 148 168 24 32 64 128 256), losses := [] }

theorem u5551 : Upper (D 1) (R 1) [304,68,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5551
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5552 : Route 9 := (fun mask => (mask,id))

def c5552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5552 : Upper (D 1) (R 1) [304,68,144,160,64] 13 := by
  apply FastRouting.sound _ _ [304,68,144,160,64] 13 (by decide) (choices 1) [1,2,8] r5552 c5552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1997
  · exact u1998
  · exact u1999

def b5553 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 305 70 148 200 17 42 106 170 298), lower := (rows 305 70 148 200 17 32 64 128 256), losses := [] }

theorem u5553 : Upper (D 1) (R 1) [304,68,144,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5553
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5554 : PairBound 9 := { available := 43, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 148 200 18 43 107 171 299), lower := (rows 305 70 148 200 18 32 64 128 256), losses := [] }

theorem u5554 : Upper (D 1) (R 1) [304,68,144,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5554
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5555 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 305 70 148 200 24 35 99 163 291), lower := (rows 305 70 148 200 24 32 64 128 256), losses := [] }

theorem u5555 : Upper (D 1) (R 1) [304,68,144,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5555
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5556 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 148 200 48 43 75 139 267), lower := (rows 305 70 148 200 48 32 64 128 256), losses := [] }

theorem u5556 : Upper (D 1) (R 1) [304,68,144,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5556
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5557 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 14 18 224 224 224 480), lower := (rows 305 82 13 14 18 32 64 128 256), losses := [] }

theorem u5557 : Upper (D 1) (R 1) [304,80,9,6,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5557
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5558 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 14 48 226 194 194 450), lower := (rows 305 82 13 14 48 32 64 128 256), losses := [] }

theorem u5558 : Upper (D 1) (R 1) [304,80,9,6,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5558
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5559 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 13 14 80 162 226 162 418), lower := (rows 305 82 13 14 80 32 64 128 256), losses := [] }

theorem u5559 : Upper (D 1) (R 1) [304,80,9,6,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5559
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5560 : Route 9 := (fun mask => (mask,id))

def c5560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5560 : Upper (D 1) (R 1) [304,80,9,6,128] 13 := by
  apply FastRouting.sound _ _ [304,80,9,6,128] 13 (by decide) (choices 1) [2,64,128] r5560 c5560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2000
  · exact u2001
  · exact u2002

def b5561 : PairBound 9 := { available := 228, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 138 18 228 228 228 484), lower := (rows 305 82 13 138 18 32 64 128 256), losses := [] }

theorem u5561 : Upper (D 1) (R 1) [304,80,9,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5561
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5562 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 82 13 138 20 226 226 226 482), lower := (rows 305 82 13 138 20 32 64 128 256), losses := [] }

theorem u5562 : Upper (D 1) (R 1) [304,80,9,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5562
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5563 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 138 48 230 198 198 454), lower := (rows 305 82 13 138 48 32 64 128 256), losses := [] }

theorem u5563 : Upper (D 1) (R 1) [304,80,9,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5563
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5564 : PairBound 9 := { available := 166, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 13 138 80 166 230 166 422), lower := (rows 305 82 13 138 80 32 64 128 256), losses := [] }

theorem u5564 : Upper (D 1) (R 1) [304,80,9,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5564
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5565 : Route 9 := (fun mask => (mask,id))

def c5565 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5565 : Upper (D 1) (R 1) [304,80,9,130,128] 13 := by
  apply FastRouting.sound _ _ [304,80,9,130,128] 13 (by decide) (choices 1) [2,4,64] r5565 c5565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2003
  · exact u2004
  · exact u2005

def b5566 : PairBound 9 := { available := 226, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 140 18 226 226 226 482), lower := (rows 305 82 13 140 18 32 64 128 256), losses := [] }

theorem u5566 : Upper (D 1) (R 1) [304,80,9,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5566
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5567 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 140 48 226 194 194 450), lower := (rows 305 82 13 140 48 32 64 128 256), losses := [] }

theorem u5567 : Upper (D 1) (R 1) [304,80,9,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5567
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5568 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 13 140 80 162 226 162 418), lower := (rows 305 82 13 140 80 32 64 128 256), losses := [] }

theorem u5568 : Upper (D 1) (R 1) [304,80,9,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5568
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5569 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 305 82 13 140 144 98 98 226 354), lower := (rows 305 82 13 140 144 32 64 128 256), losses := [] }

theorem u5569 : Upper (D 1) (R 1) [304,80,9,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5569
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5570 : PairBound 9 := { available := 166, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 200 18 166 230 166 422), lower := (rows 305 82 13 200 18 32 64 128 256), losses := [] }

theorem u5570 : Upper (D 1) (R 1) [304,80,9,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5570
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5571 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 305 82 13 200 20 162 226 162 418), lower := (rows 305 82 13 200 20 32 64 128 256), losses := [] }

theorem u5571 : Upper (D 1) (R 1) [304,80,9,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5571
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5572 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 200 48 166 198 134 390), lower := (rows 305 82 13 200 48 32 64 128 256), losses := [] }

theorem u5572 : Upper (D 1) (R 1) [304,80,9,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5572
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5573 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 13 200 144 38 102 166 294), lower := (rows 305 82 13 200 144 32 64 128 256), losses := [] }

theorem u5573 : Upper (D 1) (R 1) [304,80,9,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5573
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5574 : PairBound 9 := { available := 228, camps := [{ cop := 6, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 14 137 18 228 228 228 484), lower := (rows 305 82 14 137 18 32 64 128 256), losses := [] }

theorem u5574 : Upper (D 1) (R 1) [304,80,10,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5574
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5575 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 82 14 137 20 226 226 226 482), lower := (rows 305 82 14 137 20 32 64 128 256), losses := [] }

theorem u5575 : Upper (D 1) (R 1) [304,80,10,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5575
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5576 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 82 14 137 48 230 198 198 454), lower := (rows 305 82 14 137 48 32 64 128 256), losses := [] }

theorem u5576 : Upper (D 1) (R 1) [304,80,10,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5576
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b5577 : PairBound 9 := { available := 166, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6)], upper := (rows 305 82 14 137 80 166 230 166 422), lower := (rows 305 82 14 137 80 32 64 128 256), losses := [] }

theorem u5577 : Upper (D 1) (R 1) [304,80,10,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5577
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r5578 : Route 9 := (fun mask => (mask,id))

def c5578 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5578 : Upper (D 1) (R 1) [304,80,10,129,128] 13 := by
  apply FastRouting.sound _ _ [304,80,10,129,128] 13 (by decide) (choices 1) [2,4,64] r5578 c5578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2006
  · exact u2007
  · exact u2008

def b5579 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 305 82 14 140 17 226 226 226 482), lower := (rows 305 82 14 140 17 32 64 128 256), losses := [] }

theorem u5579 : Upper (D 1) (R 1) [304,80,10,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b5579
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u5579
end Delivery.IrregularNine14.P01
